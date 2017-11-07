/* -*- Mode:C++; c-file-style:"gnu"; indent-tabs-mode:nil; -*- */
/**
 * Copyright (c) 2014-2016,  Regents of the University of California,
 *                           Arizona Board of Regents,
 *                           Colorado State University,
 *                           University Pierre & Marie Curie, Sorbonne University,
 *                           Washington University in St. Louis,
 *                           Beijing Institute of Technology,
 *                           The University of Memphis.
 *
 * This file is part of NFD (Named Data Networking Forwarding Daemon).
 * See AUTHORS.md for complete list of NFD authors and contributors.
 *
 * NFD is free software: you can redistribute it and/or modify it under the terms
 * of the GNU General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 *
 * NFD is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * NFD, e.g., in COPYING.md file.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "forwarder.hpp"
#include "algorithm.hpp"
#include "core/logger.hpp"
#include "strategy.hpp"
#include "table/cleanup.hpp"
#include <ndn-cxx/lp/tags.hpp>
#include "face/null-face.hpp"
#include <boost/random/uniform_int_distribution.hpp>
#include "core/random.hpp"
#include <math.h>

namespace nfd {

NFD_LOG_INIT("Forwarder");

// some inline functions for geo-forwarding calculating
static inline double
getRandomNumber(double start, double end)
{
  std::uniform_real_distribution<double> dist(start, end);
  return dist(getGlobalRng());
}

static inline
double dist(uint32_t Xsrc, uint32_t Ysrc, uint32_t Xdest, uint32_t Ydest)
{
  return static_cast<double>((Xsrc - Xdest) * (Xsrc - Xdest) + (Ysrc - Ydest) * (Ysrc - Ydest));
}

static inline 
bool ifGeoForwarding(uint32_t src, uint32_t self, uint32_t dest) {
  uint32_t Xself = (self / 10000) * 10;
  uint32_t Yself = (self % 10000) * 10;
  uint32_t Xsrc = (src / 10000) * 10;
  uint32_t Ysrc = (src % 10000) * 10;
  uint32_t Xdest = (dest / 10000) * 10;
  uint32_t Ydest = (dest % 10000) * 10;
  return dist(Xself, Yself, Xdest, Ydest) <= dist(Xsrc, Ysrc, Xdest, Ydest);
}

static inline
double calculateSD(uint32_t src, uint32_t self, uint32_t dest) {
  uint32_t Xself = (self / 10000) * 10;
  uint32_t Yself = (self % 10000) * 10;
  uint32_t Xsrc = (src / 10000) * 10;
  uint32_t Ysrc = (src % 10000) * 10;
  uint32_t Xdest = (dest / 10000) * 10;
  uint32_t Ydest = (dest % 10000) * 10;
  return static_cast<double>((dist(Xsrc, Ysrc, Xself, Yself) +
                              dist(Xsrc, Ysrc, Xdest, Ydest) -
                              dist(Xself, Yself, Xdest, Ydest)) / 
                             (2 * sqrt(dist(Xsrc, Ysrc, Xdest, Ydest)) * sqrt(dist(Xsrc, Ysrc, Xself, Yself)))
                            );
}

Forwarder::Forwarder()
  : m_unsolicitedDataPolicy(new fw::DefaultUnsolicitedDataPolicy())
  , m_fib(m_nameTree)
  , m_pit(m_nameTree)
  , m_measurements(m_nameTree)
  , m_strategyChoice(m_nameTree, fw::makeDefaultStrategy(*this))
  , m_csFace(face::makeNullFace(FaceUri("contentstore://")))
{
  fw::installStrategies(*this);
  getFaceTable().addReserved(m_csFace, face::FACEID_CONTENT_STORE);

  m_faceTable.afterAdd.connect([this] (Face& face) {
    face.afterReceiveInterest.connect(
      [this, &face] (const Interest& interest) {
        this->startProcessInterest(face, interest);
      });
    face.afterReceiveData.connect(
      [this, &face] (const Data& data) {
        this->startProcessData(face, data);
      });
    face.afterReceiveNack.connect(
      [this, &face] (const lp::Nack& nack) {
        this->startProcessNack(face, nack);
      });
  });

  m_faceTable.beforeRemove.connect([this] (Face& face) {
    cleanupOnFaceRemoval(m_nameTree, m_fib, m_pit, face);
  });

  is_sleeping = false;
}

Forwarder::~Forwarder() = default;

void
Forwarder::startProcessInterest(Face& face, const Interest& interest)
{
  // print fib info
  /*
  NFD_LOG_DEBUG("print FIB info ----------------------------------");
  const fib::Entry& fibEntry = m_fib.findLongestPrefixMatch(interest.getName());
  const fib::NextHopList& nexthops = fibEntry.getNextHops();
  for (fib::NextHopList::const_iterator it = nexthops.begin(); it != nexthops.end(); ++it) {
    Face& outFace = it->getFace();  
    NFD_LOG_DEBUG(interest.getName() << " --next hop-- " << outFace.getId());
  }
  NFD_LOG_DEBUG("print FIB info ----------------------------------");
  */

  if (is_sleeping == false || m_geoTag == 0) {
    // check fields used by forwarding are well-formed
    try {
      if (interest.hasLink()) {
        interest.getLink();
      }
    }
    catch (const tlv::Error&) {
      NFD_LOG_DEBUG("startProcessInterest face=" << face.getId() <<
                    " interest=" << interest.getName() << " malformed");
      // It's safe to call interest.getName() because Name has been fully parsed
      return;
    }

    if (face.getScope() == ndn::nfd::FACE_SCOPE_LOCAL) {
      this->onIncomingInterest(face, interest);
      return;
    }

    /* test the wifi range*/
    const Name test = Name("/ndn/testRange");
    if (interest.getName().compare(0, 2, test) == 0) {
      std::cout << "Node(" << m_geoTag << ") receive test signal!" << std::endl;
      return;
    }

    // if the interest is under 'ndn/geoForwarding', go to onIncomingGeoInterest() step
    // if the interest is under '/ndn/sleep_signal', go to onIncomingSleepSignal() step
    const Name geoPrefix = Name("/ndn/geoForwarding");
    const Name sleepSignalPrefix = Name("/ndn/sleep_signal");
    const Name vsyncInterest = Name("/ndn/vsync");
    const Name vsyncData = Name("ndn/vsyncData");

    if (interest.getName().compare(0, 2, geoPrefix) == 0) {
      const name::Component& destGeoTagComponent = interest.getName().get(-1);
      uint32_t destGeoTag = boost::lexical_cast<uint32_t>(destGeoTagComponent.toUri());
      if (destGeoTag == m_geoTag) {
        // if the node is the dest target or src, not go to geo-forwarding pipeline!
        this->onIncomingInterest(face, interest);
      }
      else {
        BOOST_ASSERT(interest.getGeoTag() != ndn::DEFAULT_GEOTAG);
        NFD_LOG_DEBUG("go to geoForwarding pipeline!");
        // copy interest ! because we want to modify the interest
        shared_ptr<Interest> interest_ = make_shared<Interest>(interest.wireEncode());
        //Interest interest_(interest.wireEncode());
        this->onIncomingGeoInterest(face, *interest_);
      }
    }
    else if (interest.getName().compare(0, 2, sleepSignalPrefix) == 0) {
      this->onIncomingSleepSignal(face, interest);
    }
    else if (interest.getName().compare(0, 2, vsyncInterest) == 0 ||
             interest.getName().compare(0, 2, vsyncData) == 0) {
      auto vid = interest.getName().get(-3).toUri();
      if (vid != std::to_string(m_geoTag)) return;
      else this->onIncomingInterest(face, interest);
    }
    else {
      this->onIncomingInterest(face, interest);
    }
  }
}

void
Forwarder::startProcessData(Face& face, const Data& data)
{
  // check fields used by forwarding are well-formed
  // (none needed)
  // if the packet is under 'ndn/geoForwarding', go to onIncomingGeoData() step
  if (is_sleeping == false || m_geoTag == 0) {
    NFD_LOG_DEBUG("entering into startProcessData()");
    const Name geoPrefix = Name("/ndn/geoForwarding");
    const Name geo2Prefix = Name("/ndn/geoForwarding2");
    const Name geo3Prefix = Name("/ndn/geoForwarding3");
    //this->onIncomingData(face, data);
    
    if (data.getName().compare(0, 2, geoPrefix) == 0 ||
        data.getName().compare(0, 2, geo2Prefix) == 0 ||
        data.getName().compare(0, 2, geo3Prefix) == 0) {
      if (m_geoTag == 0) this->onIncomingData(face, data);
      else {
        NFD_LOG_DEBUG("go to geoForwarding pipeline!");
        this->onIncomingGeoData(face, data);
      }
    }
    else this->onIncomingData(face, data);
    
  }
  //this->onIncomingData(face, data);
}

void
Forwarder::startProcessNack(Face& face, const lp::Nack& nack)
{
  // check fields used by forwarding are well-formed
  try {
    if (nack.getInterest().hasLink()) {
      nack.getInterest().getLink();
    }
  }
  catch (const tlv::Error&) {
    NFD_LOG_DEBUG("startProcessNack face=" << face.getId() <<
                  " nack=" << nack.getInterest().getName() <<
                  "~" << nack.getReason() << " malformed");
    return;
  }

  this->onIncomingNack(face, nack);
}

void
Forwarder::onIncomingInterest(Face& inFace, const Interest& interest)
{
  // receive Interest
  NFD_LOG_DEBUG("onIncomingInterest face=" << inFace.getId() <<
                " interest=" << interest.getName());
  interest.setTag(make_shared<lp::IncomingFaceIdTag>(inFace.getId()));
  ++m_counters.nInInterests;
  //std::cout << "inInterests = " << m_counters.nInInterests << std::endl;

  // /localhost scope control
  bool isViolatingLocalhost = inFace.getScope() == ndn::nfd::FACE_SCOPE_NON_LOCAL &&
                              scope_prefix::LOCALHOST.isPrefixOf(interest.getName());
  if (isViolatingLocalhost) {
    NFD_LOG_DEBUG("onIncomingInterest face=" << inFace.getId() <<
                  " interest=" << interest.getName() << " violates /localhost");
    // (drop)
    return;
  }

  // detect duplicate Nonce with Dead Nonce List
  bool hasDuplicateNonceInDnl = m_deadNonceList.has(interest.getName(), interest.getNonce());
  if (hasDuplicateNonceInDnl) {
    // goto Interest loop pipeline
    this->onInterestLoop(inFace, interest);
    return;
  }

  // forwarding strategy2
  const Name geo2 = Name("/ndn/geoForwarding2");
  if (interest.getName().compare(0, 2, geo2) == 0) {
    uint32_t srcGeoTag = interest.getGeoTag();
    BOOST_ASSERT(srcGeoTag != ndn::DEFAULT_GEOTAG);
    uint32_t lastGeo = interest.getLastGeo();
    BOOST_ASSERT(lastGeo != ndn::DEFAULT_LASTGEO);
    const Name& name = interest.getName();
    bool isEndWithDigest = name.size() > 0 && name[-1].isImplicitSha256Digest();
    const name::Component& destGeoTagComponent = isEndWithDigest ? name.get(-2) : name.get(-1);
    uint32_t destGeoTag = boost::lexical_cast<uint32_t>(destGeoTagComponent.toUri());

    if (!ifGeoForwarding(lastGeo, m_geoTag, destGeoTag)) {
      //std::cout << "Farther to dest than last node, Drop interest" << std::endl;
      return;
    }
  }

  // forwarding strategy3
  const Name geo3 = Name("/ndn/geoForwarding3");
  if (interest.getName().compare(0, 2, geo3) == 0) {
    uint32_t srcGeoTag = interest.getGeoTag();
    BOOST_ASSERT(srcGeoTag != ndn::DEFAULT_GEOTAG);
    uint32_t lastGeo = interest.getLastGeo();
    BOOST_ASSERT(lastGeo != ndn::DEFAULT_LASTGEO);
    const Name& name = interest.getName();
    bool isEndWithDigest = name.size() > 0 && name[-1].isImplicitSha256Digest();
    const name::Component& destGeoTagComponent = isEndWithDigest ? name.get(-2) : name.get(-1);
    uint32_t destGeoTag = boost::lexical_cast<uint32_t>(destGeoTagComponent.toUri());

    double sd = calculateSD(srcGeoTag, m_geoTag, destGeoTag);
    double d_range = 0.8;
    if (sd <= d_range) {
      std::cout << "sd is too small, Drop interest" << std::endl;
      return;
    }
  }

  // PIT insert
  // if 'ndn/vsync/group_id/vector' or 'ndn/vsyncData', check if exists similar interest
  /*
  const auto& n = interest.getName();
  if (n.compare(0, 2, "/ndn/vsyncData") == 0)
  {
    shared_ptr<pit::Entry> pitEntry = m_pit.find(interest);
    if (pitEntry != nullptr) return;
  }
  */
  shared_ptr<pit::Entry> pitEntry = m_pit.insert(interest).first;

  // detect duplicate Nonce in PIT entry
  bool hasDuplicateNonceInPit = fw::findDuplicateNonce(*pitEntry, interest.getNonce(), inFace) !=
                                fw::DUPLICATE_NONCE_NONE;
  if (hasDuplicateNonceInPit) {
    // goto Interest loop pipeline
    this->onInterestLoop(inFace, interest);
    return;
  }

  // cancel unsatisfy & straggler timer
  this->cancelUnsatisfyAndStragglerTimer(*pitEntry);

  const pit::InRecordCollection& inRecords = pitEntry->getInRecords();
  bool isPending = inRecords.begin() != inRecords.end();
  if (!isPending) {
    if (m_csFromNdnSim == nullptr) {
      m_cs.find(interest,
                bind(&Forwarder::onContentStoreHit, this, ref(inFace), pitEntry, _1, _2),
                bind(&Forwarder::onContentStoreMiss, this, ref(inFace), pitEntry, _1));
    }
    else {
      shared_ptr<Data> match = m_csFromNdnSim->Lookup(interest.shared_from_this());
      if (match != nullptr) {
        this->onContentStoreHit(inFace, pitEntry, interest, *match);
      }
      else {
        this->onContentStoreMiss(inFace, pitEntry, interest);
      }
    }
  }
  else {
    this->onContentStoreMiss(inFace, pitEntry, interest);
  }
}

void
Forwarder::onInterestLoop(Face& inFace, const Interest& interest)
{
  // if multi-access face, drop
  if (inFace.getLinkType() == ndn::nfd::LINK_TYPE_MULTI_ACCESS) {
    NFD_LOG_DEBUG("onInterestLoop face=" << inFace.getId() <<
                  " interest=" << interest.getName() <<
                  " drop");
    return;
  }

  NFD_LOG_DEBUG("onInterestLoop face=" << inFace.getId() <<
                " interest=" << interest.getName() <<
                " send-Nack-duplicate");

  // send Nack with reason=DUPLICATE
  // note: Don't enter outgoing Nack pipeline because it needs an in-record.
  lp::Nack nack(interest);
  nack.setReason(lp::NackReason::DUPLICATE);
  inFace.sendNack(nack);
}

void
Forwarder::onContentStoreMiss(const Face& inFace, const shared_ptr<pit::Entry>& pitEntry,
                              const Interest& interest)
{
  NFD_LOG_DEBUG("onContentStoreMiss interest=" << interest.getName());
  const auto& n = interest.getName();

  if (interest.getName().compare(0, 2, "/ndn/vsyncData") == 0)
  {
    if (m_vst.find(interest) != nullptr) {
      std::cout << "not send the vsyncData interest!" << std::endl;
      auto vstEntry = m_vst.find(interest);
      scheduler::cancel(vstEntry->m_scheduleInterestTimer);
      return;
    }
    uint64_t t_vsync = getRandomNumber(50, 1000);
    pitEntry->insertOrUpdateInRecord(const_cast<Face&>(inFace), interest, t_vsync);

    // first forward to the local app
    std::set<Face*> pendingUpstreams;
    const fib::Entry& fibEntry = m_fib.findLongestPrefixMatch(interest.getName());
    const fib::NextHopList& nexthops = fibEntry.getNextHops();
    for (fib::NextHopList::const_iterator it = nexthops.begin(); it != nexthops.end(); ++it) {
      Face& outFace = it->getFace();  
      //NFD_LOG_DEBUG(interest.getName() << " --next hop-- " << outFace.getId());
      if (outFace.getScope() == ndn::nfd::FACE_SCOPE_LOCAL) {
        // ignore the interests coming from local app
        if (inFace.getScope() == ndn::nfd::FACE_SCOPE_LOCAL) continue;
        this->onOutgoingInterest(pitEntry, outFace, interest);
        continue;
      }
      pendingUpstreams.insert(&it->getFace());
    }

    if (!pendingUpstreams.empty()) {
      NFD_LOG_DEBUG("set vst entry for interest = " << interest.getName());
      shared_ptr<vst::Entry> vstEntry = m_vst.insert(interest);
      BOOST_ASSERT(vstEntry != nullptr);
      vstEntry->m_scheduleInterestTimer = scheduler::schedule(time::milliseconds(t_vsync), 
        bind(&Forwarder::onVstSchedulerTimeout, this, ref(inFace), pitEntry, vstEntry, cref(interest), pendingUpstreams));
      return;
    }
  }

  // insert in-record
  pitEntry->insertOrUpdateInRecord(const_cast<Face&>(inFace), interest);

  // set PIT unsatisfy timer
  this->setUnsatisfyTimer(pitEntry);

  // has NextHopFaceId?
  shared_ptr<lp::NextHopFaceIdTag> nextHopTag = interest.getTag<lp::NextHopFaceIdTag>();
  if (nextHopTag != nullptr) {
    // chosen NextHop face exists?
    Face* nextHopFace = m_faceTable.get(*nextHopTag);
    if (nextHopFace != nullptr) {
      NFD_LOG_DEBUG("onContentStoreMiss interest=" << interest.getName() << " nexthop-faceid=" << nextHopFace->getId());
      // go to outgoing Interest pipeline
      // scope control is unnecessary, because privileged app explicitly wants to forward
      this->onOutgoingInterest(pitEntry, *nextHopFace, interest);
    }
    return;
  }

  // dispatch to strategy: after incoming Interest
  this->dispatchToStrategy(*pitEntry,
    [&] (fw::Strategy& strategy) { 
      NFD_LOG_DEBUG("Using Strategy = " << strategy.getName());
      strategy.afterReceiveInterest(inFace, interest, pitEntry); });
}

void 
Forwarder::onVstSchedulerTimeout(const Face& inFace, const shared_ptr<pit::Entry>& pitEntry,
                                 const shared_ptr<vst::Entry>& vstEntry, const Interest& interest,
                                 std::set<Face*> pendingUpstreams)
{
  NFD_LOG_DEBUG("onVstSchedulerTimeout interest=" << interest.getName());
  // in case the pit has been deleted
  if (vstEntry->isSatisfied()) {
    NFD_LOG_DEBUG("pitEntry has been satisfied!");
    m_vst.erase(vstEntry.get());
    return;
  }

  m_vst.erase(vstEntry.get());
  /*
  name_tree::Entry* nte = m_nameTree.getEntry(*pitEntry);
  if (nte == nullptr) {
    NFD_LOG_DEBUG("pitEntry has been satisfied!");
    return;
  }
  */

  this->setUnsatisfyTimer(pitEntry);

  // has NextHopFaceId?
  /*
  shared_ptr<lp::NextHopFaceIdTag> nextHopTag = interest.getTag<lp::NextHopFaceIdTag>();
  if (nextHopTag != nullptr) {
    // chosen NextHop face exists?
    Face* nextHopFace = m_faceTable.get(*nextHopTag);
    if (nextHopFace != nullptr) {
      NFD_LOG_DEBUG("onContentStoreMiss interest=" << interest.getName() << " nexthop-faceid=" << nextHopFace->getId());
      // go to outgoing Interest pipeline
      // scope control is unnecessary, because privileged app explicitly wants to forward
      this->onOutgoingInterest(pitEntry, *nextHopFace, interest);
    }
    return;
  }

  // dispatch to strategy: after incoming Interest
  this->dispatchToStrategy(*pitEntry,
    [&] (fw::Strategy& strategy) { 
      NFD_LOG_DEBUG("Using Strategy = " << strategy.getName());
      strategy.afterReceiveInterest(inFace, interest, pitEntry); });
  */

  // foreach pending upstream
  for (Face* pendingUpstream : pendingUpstreams) {
    // goto outgoing Interest pipeline
    this->onOutgoingInterest(pitEntry, *pendingUpstream, interest);
  }
}


void
Forwarder::onContentStoreHit(const Face& inFace, const shared_ptr<pit::Entry>& pitEntry,
                             const Interest& interest, const Data& data)
{
  NFD_LOG_DEBUG("onContentStoreHit interest=" << interest.getName());

  beforeSatisfyInterest(*pitEntry, *m_csFace, data);
  this->dispatchToStrategy(*pitEntry,
    [&] (fw::Strategy& strategy) { strategy.beforeSatisfyInterest(pitEntry, *m_csFace, data); });

  data.setTag(make_shared<lp::IncomingFaceIdTag>(face::FACEID_CONTENT_STORE));
  // XXX should we lookup PIT for other Interests that also match csMatch?

  // set PIT straggler timer
  this->setStragglerTimer(pitEntry, true, data.getFreshnessPeriod());

  // goto outgoing Data pipeline
  this->onOutgoingData(data, *const_pointer_cast<Face>(inFace.shared_from_this()));
}

void
Forwarder::onOutgoingInterest(const shared_ptr<pit::Entry>& pitEntry, Face& outFace, const Interest& interest)
{
  NFD_LOG_DEBUG("onOutgoingInterest face=" << outFace.getId() <<
                " interest=" << pitEntry->getName());

  // insert out-record
  pitEntry->insertOrUpdateOutRecord(outFace, interest);

  // send Interest
  outFace.sendInterest(interest);
  ++m_counters.nOutInterests;
  //std::cout << "outInterests = " << m_counters.nInInterests << std::endl;
}

void
Forwarder::onInterestReject(const shared_ptr<pit::Entry>& pitEntry)
{
  if (fw::hasPendingOutRecords(*pitEntry)) {
    NFD_LOG_ERROR("onInterestReject interest=" << pitEntry->getName() <<
                  " cannot reject forwarded Interest");
    return;
  }
  NFD_LOG_DEBUG("onInterestReject interest=" << pitEntry->getName());

  // cancel unsatisfy & straggler timer
  this->cancelUnsatisfyAndStragglerTimer(*pitEntry);

  // set PIT straggler timer
  this->setStragglerTimer(pitEntry, false);
}

void
Forwarder::onInterestUnsatisfied(const shared_ptr<pit::Entry>& pitEntry)
{
  NFD_LOG_DEBUG("onInterestUnsatisfied interest=" << pitEntry->getName());

  // invoke PIT unsatisfied callback
  beforeExpirePendingInterest(*pitEntry);
  this->dispatchToStrategy(*pitEntry,
    [&] (fw::Strategy& strategy) { strategy.beforeExpirePendingInterest(pitEntry); });

  // goto Interest Finalize pipeline
  this->onInterestFinalize(pitEntry, false);
}

void
Forwarder::onInterestFinalize(const shared_ptr<pit::Entry>& pitEntry, bool isSatisfied,
                              time::milliseconds dataFreshnessPeriod)
{
  NFD_LOG_DEBUG("node(" << m_geoTag << ") onInterestFinalize interest=" << pitEntry->getName() <<
                (isSatisfied ? " satisfied" : " unsatisfied"));

  // Dead Nonce List insert if necessary
  this->insertDeadNonceList(*pitEntry, isSatisfied, dataFreshnessPeriod, 0);

  // PIT delete
  this->cancelUnsatisfyAndStragglerTimer(*pitEntry);
  m_pit.erase(pitEntry.get());
}

void
Forwarder::onIncomingData(Face& inFace, const Data& data)
{
  // receive Data
  NFD_LOG_DEBUG("onIncomingData face=" << inFace.getId() << " data=" << data.getName());
  data.setTag(make_shared<lp::IncomingFaceIdTag>(inFace.getId()));
  ++m_counters.nInData;

  // /localhost scope control
  bool isViolatingLocalhost = inFace.getScope() == ndn::nfd::FACE_SCOPE_NON_LOCAL &&
                              scope_prefix::LOCALHOST.isPrefixOf(data.getName());
  if (isViolatingLocalhost) {
    NFD_LOG_DEBUG("onIncomingData face=" << inFace.getId() <<
                  " data=" << data.getName() << " violates /localhost");
    // (drop)
    return;
  }

  // PIT match
  pit::DataMatchResult pitMatches = m_pit.findAllDataMatches(data);
  if (pitMatches.begin() == pitMatches.end()) {
    // goto Data unsolicited pipeline
    this->onDataUnsolicited(inFace, data);
    return;
  }

  shared_ptr<Data> dataCopyWithoutTag = make_shared<Data>(data);
  dataCopyWithoutTag->removeTag<lp::HopCountTag>();

  // CS insert
  if (m_csFromNdnSim == nullptr)
    m_cs.insert(*dataCopyWithoutTag);
  else
    m_csFromNdnSim->Add(dataCopyWithoutTag);

  std::set<Face*> pendingDownstreams;
  // foreach PitEntry
  auto now = time::steady_clock::now();
  for (const shared_ptr<pit::Entry>& pitEntry : pitMatches) {
    NFD_LOG_DEBUG("onIncomingData matching=" << pitEntry->getName());

    // cancel unsatisfy & straggler timer
    this->cancelUnsatisfyAndStragglerTimer(*pitEntry);

    // remember pending downstreams
    for (const pit::InRecord& inRecord : pitEntry->getInRecords()) {
      NFD_LOG_DEBUG("inRecord face=" << inRecord.getFace().getId());
      if (inRecord.getExpiry() > now) {
        NFD_LOG_DEBUG("outGoingData to face=" << inRecord.getFace().getId());
        pendingDownstreams.insert(&inRecord.getFace());
      }
    }

    // invoke PIT satisfy callback
    beforeSatisfyInterest(*pitEntry, inFace, data);
    this->dispatchToStrategy(*pitEntry,
      [&] (fw::Strategy& strategy) { strategy.beforeSatisfyInterest(pitEntry, inFace, data); });

    // Dead Nonce List insert if necessary (for out-record of inFace)
    this->insertDeadNonceList(*pitEntry, true, data.getFreshnessPeriod(), &inFace);

    // mark PIT satisfied
    pitEntry->clearInRecords();
    pitEntry->deleteOutRecord(inFace);

    // set PIT straggler timer
    this->setStragglerTimer(pitEntry, true, data.getFreshnessPeriod());

    // update the vst entry
    shared_ptr<vst::Entry> vstEntry = m_vst.find(data.getName());
    if (vstEntry != nullptr) {
      vstEntry->setSatisfied();
    }
  }

  // foreach pending downstream
  for (Face* pendingDownstream : pendingDownstreams) {
    /* Since we use wifi only one interface. To realize broadcast, we need to comment out this.*/
    /*
    if (pendingDownstream == &inFace) {
      continue;
    }
    */
    // goto outgoing Data pipeline
    this->onOutgoingData(data, *pendingDownstream);
  }
}

void
Forwarder::onDataUnsolicited(Face& inFace, const Data& data)
{
  // accept to cache?
  fw::UnsolicitedDataDecision decision = m_unsolicitedDataPolicy->decide(inFace, data);
  if (decision == fw::UnsolicitedDataDecision::CACHE) {
    // CS insert
    if (m_csFromNdnSim == nullptr)
      m_cs.insert(data, true);
    else
      m_csFromNdnSim->Add(data.shared_from_this());
  }

  NFD_LOG_DEBUG("onDataUnsolicited face=" << inFace.getId() <<
                " data=" << data.getName() <<
                " decision=" << decision);
}

void
Forwarder::onOutgoingData(const Data& data, Face& outFace)
{
  if (outFace.getId() == face::INVALID_FACEID) {
    NFD_LOG_WARN("onOutgoingData face=invalid data=" << data.getName());
    return;
  }
  NFD_LOG_DEBUG("node(" << m_geoTag << ")" << "onOutgoingData face=" << outFace.getId() 
                << " data=" << data.getName());
  //std::cout << "node(" << m_geoTag << ")" "onOutGoingData!" << std::endl;

  // /localhost scope control
  bool isViolatingLocalhost = outFace.getScope() == ndn::nfd::FACE_SCOPE_NON_LOCAL &&
                              scope_prefix::LOCALHOST.isPrefixOf(data.getName());
  if (isViolatingLocalhost) {
    NFD_LOG_DEBUG("onOutgoingData face=" << outFace.getId() <<
                  " data=" << data.getName() << " violates /localhost");
    // (drop)
    return;
  }

  // TODO traffic manager

  // send Data
  NFD_LOG_DEBUG("before sending the data!");
  outFace.sendData(data);
  ++m_counters.nOutData;
}

void
Forwarder::onIncomingNack(Face& inFace, const lp::Nack& nack)
{
  // receive Nack
  nack.setTag(make_shared<lp::IncomingFaceIdTag>(inFace.getId()));
  ++m_counters.nInNacks;

  // if multi-access face, drop
  if (inFace.getLinkType() == ndn::nfd::LINK_TYPE_MULTI_ACCESS) {
    
    NFD_LOG_DEBUG("onIncomingNack face=" << inFace.getId() <<
                  " nack=" << nack.getInterest().getName() <<
                  "~" << nack.getReason() << " face-is-multi-access");
    
    return;
  }

  // PIT match
  shared_ptr<pit::Entry> pitEntry = m_pit.find(nack.getInterest());
  // if no PIT entry found, drop
  if (pitEntry == nullptr) {
    
    NFD_LOG_DEBUG("onIncomingNack face=" << inFace.getId() <<
                  " nack=" << nack.getInterest().getName() <<
                  "~" << nack.getReason() << " no-PIT-entry");
    
    return;
  }

  // has out-record?
  pit::OutRecordCollection::iterator outRecord = pitEntry->getOutRecord(inFace);
  // if no out-record found, drop
  if (outRecord == pitEntry->out_end()) {
    
    NFD_LOG_DEBUG("onIncomingNack face=" << inFace.getId() <<
                  " nack=" << nack.getInterest().getName() <<
                  "~" << nack.getReason() << " no-out-record");
    
    return;
  }

  // if out-record has different Nonce, drop
  if (nack.getInterest().getNonce() != outRecord->getLastNonce()) {
    
    NFD_LOG_DEBUG("onIncomingNack face=" << inFace.getId() <<
                  " nack=" << nack.getInterest().getName() <<
                  "~" << nack.getReason() << " wrong-Nonce " <<
                  nack.getInterest().getNonce() << "!=" << outRecord->getLastNonce());
    
    return;
  }
  
  NFD_LOG_DEBUG("onIncomingNack face=" << inFace.getId() <<
                " nack=" << nack.getInterest().getName() <<
                "~" << nack.getReason() << " OK");
  
  // record Nack on out-record
  outRecord->setIncomingNack(nack);

  // trigger strategy: after receive NACK
  this->dispatchToStrategy(*pitEntry,
    [&] (fw::Strategy& strategy) { strategy.afterReceiveNack(inFace, nack, pitEntry); });
}

void
Forwarder::onOutgoingNack(const shared_ptr<pit::Entry>& pitEntry, const Face& outFace,
                          const lp::NackHeader& nack)
{
  if (outFace.getId() == face::INVALID_FACEID) {
    
    NFD_LOG_WARN("onOutgoingNack face=invalid" <<
                  " nack=" << pitEntry->getInterest().getName() <<
                  "~" << nack.getReason() << " no-in-record");
    
    return;
  }

  // has in-record?
  pit::InRecordCollection::iterator inRecord = pitEntry->getInRecord(outFace);

  // if no in-record found, drop
  if (inRecord == pitEntry->in_end()) {
    
    NFD_LOG_DEBUG("onOutgoingNack face=" << outFace.getId() <<
                  " nack=" << pitEntry->getInterest().getName() <<
                  "~" << nack.getReason() << " no-in-record");
    
    return;
  }

  // if multi-access face, drop
  if (outFace.getLinkType() == ndn::nfd::LINK_TYPE_MULTI_ACCESS) {
    
    NFD_LOG_DEBUG("onOutgoingNack face=" << outFace.getId() <<
                  " nack=" << pitEntry->getInterest().getName() <<
                  "~" << nack.getReason() << " face-is-multi-access");
    
    return;
  }
  
  NFD_LOG_DEBUG("onOutgoingNack face=" << outFace.getId() <<
                " nack=" << pitEntry->getInterest().getName() <<
                "~" << nack.getReason() << " OK");
  
  // create Nack packet with the Interest from in-record
  lp::Nack nackPkt(inRecord->getInterest());
  nackPkt.setHeader(nack);

  // erase in-record
  pitEntry->deleteInRecord(outFace);

  // send Nack on face
  const_cast<Face&>(outFace).sendNack(nackPkt);
  ++m_counters.nOutNacks;
}

static inline bool
compare_InRecord_expiry(const pit::InRecord& a, const pit::InRecord& b)
{
  return a.getExpiry() < b.getExpiry();
}

void
Forwarder::setUnsatisfyTimer(const shared_ptr<pit::Entry>& pitEntry)
{
  pit::InRecordCollection::iterator lastExpiring =
    std::max_element(pitEntry->in_begin(), pitEntry->in_end(), &compare_InRecord_expiry);

  time::steady_clock::TimePoint lastExpiry = lastExpiring->getExpiry();
  time::nanoseconds lastExpiryFromNow = lastExpiry - time::steady_clock::now();
  if (lastExpiryFromNow <= time::seconds::zero()) {
    // TODO all in-records are already expired; will this happen?
    NFD_LOG_DEBUG("all in-records are already expired!");
  }

  scheduler::cancel(pitEntry->m_unsatisfyTimer);
  pitEntry->m_unsatisfyTimer = scheduler::schedule(lastExpiryFromNow,
    bind(&Forwarder::onInterestUnsatisfied, this, pitEntry));
}

void
Forwarder::setStragglerTimer(const shared_ptr<pit::Entry>& pitEntry, bool isSatisfied,
                             time::milliseconds dataFreshnessPeriod)
{
  time::nanoseconds stragglerTime = time::milliseconds(100);

  scheduler::cancel(pitEntry->m_stragglerTimer);
  pitEntry->m_stragglerTimer = scheduler::schedule(stragglerTime,
    bind(&Forwarder::onInterestFinalize, this, pitEntry, isSatisfied, dataFreshnessPeriod));
}

void
Forwarder::cancelUnsatisfyAndStragglerTimer(pit::Entry& pitEntry)
{
  scheduler::cancel(pitEntry.m_unsatisfyTimer);
  scheduler::cancel(pitEntry.m_stragglerTimer);
}

static inline void
insertNonceToDnl(DeadNonceList& dnl, const pit::Entry& pitEntry,
                 const pit::OutRecord& outRecord)
{
  dnl.add(pitEntry.getName(), outRecord.getLastNonce());
}

void
Forwarder::insertDeadNonceList(pit::Entry& pitEntry, bool isSatisfied,
                               time::milliseconds dataFreshnessPeriod, Face* upstream)
{
  // need Dead Nonce List insert?
  bool needDnl = false;
  if (isSatisfied) {
    bool hasFreshnessPeriod = dataFreshnessPeriod >= time::milliseconds::zero();
    // Data never becomes stale if it doesn't have FreshnessPeriod field
    needDnl = static_cast<bool>(pitEntry.getInterest().getMustBeFresh()) &&
              (hasFreshnessPeriod && dataFreshnessPeriod < m_deadNonceList.getLifetime());
  }
  else {
    needDnl = true;
  }

  if (!needDnl) {
    return;
  }

  // Dead Nonce List insert
  if (upstream == 0) {
    // insert all outgoing Nonces
    const pit::OutRecordCollection& outRecords = pitEntry.getOutRecords();
    std::for_each(outRecords.begin(), outRecords.end(),
                  bind(&insertNonceToDnl, ref(m_deadNonceList), cref(pitEntry), _1));
  }
  else {
    // insert outgoing Nonce of a specific face
    pit::OutRecordCollection::iterator outRecord = pitEntry.getOutRecord(*upstream);
    if (outRecord != pitEntry.getOutRecords().end()) {
      m_deadNonceList.add(pitEntry.getName(), outRecord->getLastNonce());
    }
  }
}

static inline void
geoInsertNonceToDnl(DeadNonceList& dnl, const pit::Entry& pitEntry,
                    const pit::InRecord& inRecord)
{
  dnl.add(pitEntry.getName(), inRecord.getLastNonce());
}

void
Forwarder::geoOnInterestFinalize(const shared_ptr<pit::Entry>& pitEntry)
{
  NFD_LOG_DEBUG("node(" << m_geoTag << ") onInterestFinalize interest=" << pitEntry->getName() << " unsatisfied");

  // Dead Nonce List insert if necessary
  this->geoInsertDeadNonceList(*pitEntry);

  // PIT delete
  this->cancelUnsatisfyAndStragglerTimer(*pitEntry);
  m_pit.erase(pitEntry.get());
}

void 
Forwarder::geoInsertDeadNonceList(pit::Entry& pitEntry)
{
  // Dead Nonce List insert
  // insert all ingoing Nonces
  const pit::InRecordCollection& inRecords = pitEntry.getInRecords();
  std::for_each(inRecords.begin(), inRecords.end(),
                bind(&geoInsertNonceToDnl, ref(m_deadNonceList), cref(pitEntry), _1));
}

//////////////////////////////////////////////////////////////////////////////////////
/* @brief A different incoming interest pipeline for geo-forwarding                 //
 * @refrenced by forwarder::onComingInterest(Face& inFace, const Interest& interest)//
*/////////////////////////////////////////////////////////////////////////////////////
void 
Forwarder::onIncomingGeoInterest(Face& inFace, Interest& interest)
{
  // receive Interest
  NFD_LOG_DEBUG("node(" << m_geoTag << ")" << "onIncomingInterest face=" << inFace.getId() <<
                " interest=" << interest.getName());
  interest.setTag(make_shared<lp::IncomingFaceIdTag>(inFace.getId()));
  ++m_counters.nInInterests;
  //std::cout << "inInterests = " << m_counters.nInInterests << std::endl;

  // /localhost scope control
  bool isViolatingLocalhost = inFace.getScope() == ndn::nfd::FACE_SCOPE_NON_LOCAL &&
                              scope_prefix::LOCALHOST.isPrefixOf(interest.getName());
  if (isViolatingLocalhost) {
    NFD_LOG_DEBUG("onIncomingInterest face=" << inFace.getId() <<
                  " interest=" << interest.getName() << " violates /localhost");
    // (drop)
    return;
  }

  // Geo - 1. Check if same interest scheduled for transmission
  // If scheduled, remove the sitEntry, pit entry and return
  shared_ptr<sit::Entry> sitEntry = m_sit.find(interest);
  if (sitEntry != nullptr) {
    NFD_LOG_DEBUG("node(" << m_geoTag << ") sitEntry duplicates! Delete sitEntry!");
    size_t x = m_geoTag / 10000;
    size_t y = m_geoTag % 10000;
    //std::cout << "node(" << x << ", " << y << ") sitEntry duplicates! Delete pitEntry and sitEntry!" << std::endl;
    scheduler::cancel(sitEntry->m_scheduleInterestTimer);
    m_sit.erase(sitEntry.get());
    // goto Interest Finalize pipeline
    //shared_ptr<pit::Entry> pitEntry = m_pit.find(interest);
    //if (pitEntry != nullptr) this->geoOnInterestFinalize(pitEntry);
    return;
  }

  // detect duplicate Nonce with Dead Nonce List
  bool hasDuplicateNonceInDnl = m_deadNonceList.has(interest.getName(), interest.getNonce());
  if (hasDuplicateNonceInDnl) {
    // goto Interest loop pipeline
    this->onInterestLoop(inFace, interest);
    return;
  }

  // PIT insert
  shared_ptr<pit::Entry> pitEntry = m_pit.insert(interest).first;

  // detect duplicate Nonce in PIT entry
  bool hasDuplicateNonceInPit = fw::findDuplicateNonce(*pitEntry, interest.getNonce(), inFace) !=
                                fw::DUPLICATE_NONCE_NONE;
  if (hasDuplicateNonceInPit) {
    // goto Interest loop pipeline
    this->onInterestLoop(inFace, interest);
    return;
  }
  // cancel unsatisfy & straggler timer
  this->cancelUnsatisfyAndStragglerTimer(*pitEntry);

  // check cs
  const pit::InRecordCollection& inRecords = pitEntry->getInRecords();
  bool isPending = inRecords.begin() != inRecords.end();
  if (!isPending) {
    if (m_csFromNdnSim == nullptr) {
      m_cs.find(interest,
                bind(&Forwarder::onGeoContentStoreHit, this, ref(inFace), pitEntry, _1, _2, ref(interest)),
                bind(&Forwarder::onGeoContentStoreMiss, this, ref(inFace), pitEntry, _1, ref(interest)));
    }
    else {
      shared_ptr<Data> match = m_csFromNdnSim->Lookup(interest.shared_from_this());
      if (match != nullptr) {
        this->onGeoContentStoreHit(inFace, pitEntry, interest, *match, interest);
      }
      else {
        this->onGeoContentStoreMiss(inFace, pitEntry, interest, interest);
      }
    }
  }
  else {
    this->onContentStoreMiss(inFace, pitEntry, interest);
  }

}

void 
Forwarder::onGeoContentStoreMiss(Face& inFace, const shared_ptr<pit::Entry>& pitEntry,
                                 const Interest& interest_,
                                 Interest& interest)
{
  NFD_LOG_DEBUG("node(" << m_geoTag << ")" << "onGeoContentStoreMiss interest=" << interest.getName());

  // insert in-record
  pitEntry->insertOrUpdateInRecord(inFace, interest);
  // set PIT unsatisfy timer
  this->setUnsatisfyTimer(pitEntry);

  this->setSitSchedulerTimer(inFace, interest, pitEntry);
  // no dispatch to strategy: after incoming Interest
}

void
Forwarder::setSitSchedulerTimer(const Face& inFace, Interest& interest, 
                                const shared_ptr<pit::Entry>& pitEntry)
{
  NFD_LOG_DEBUG("node(" << m_geoTag << ")" << "onGeoContentStoreMiss interest=" << interest.getName());
  uint32_t srcGeoTag = interest.getGeoTag();
  BOOST_ASSERT(srcGeoTag != ndn::DEFAULT_GEOTAG);
  uint32_t lastGeo = interest.getLastGeo();
  BOOST_ASSERT(lastGeo != ndn::DEFAULT_LASTGEO);

  const Name& name = interest.getName();
  bool isEndWithDigest = name.size() > 0 && name[-1].isImplicitSha256Digest();
  const name::Component& destGeoTagComponent = isEndWithDigest ? name.get(-2) : name.get(-1);
  uint32_t destGeoTag = boost::lexical_cast<uint32_t>(destGeoTagComponent.toUri());

  NFD_LOG_DEBUG("srcGeoTag(" << srcGeoTag << ") m_geoTag(" << m_geoTag << ") lastGeoTag(" << lastGeo << ") destGeoTag(" << destGeoTag << ")");

  /*
  // stop processing if the receiving node is farther from the destination than the last node
  if (!ifGeoForwarding(lastGeo, m_geoTag, destGeoTag)) {
    //std::cout << "Farther to dest than last node, Drop interest" << std::endl;
    // cancel unsatisfy & straggler timer
    //this->cancelUnsatisfyAndStragglerTimer(*pitEntry);
    //m_pit.erase(pitEntry.get());
    this->geoOnInterestFinalize(pitEntry);
    return;
  }
  */

  // stop processing if the receiving node is farther from the destination than the node transmitting the Interest
  if (!ifGeoForwarding(srcGeoTag, m_geoTag, destGeoTag)) {
    //std::cout << "Farther to dest than src, Drop interest" << std::endl;
    // cancel unsatisfy & straggler timer
    //this->cancelUnsatisfyAndStragglerTimer(*pitEntry);
    //m_pit.erase(pitEntry.get());
    this->geoOnInterestFinalize(pitEntry);
    return;
  }

  double sd = calculateSD(srcGeoTag, m_geoTag, destGeoTag);
  double t_fw_min = 10;
  double t_fw_max = 10;
  double d_range = 0.85;
  double t_gap = 100;
  if (sd > d_range) t_fw_max = t_fw_min * 2;
  else t_fw_max = t_fw_min * 2 + (d_range - sd) * t_gap;

  //if (sd > d_range) t_fw_max = t_fw_min * 2;
  /*else {
    t_fw_min *= 2;
    t_fw_max = t_fw_min + (d_range - sd) * t_gap;
  }*/
  uint64_t t_fw = getRandomNumber(t_fw_min, t_fw_max);
  size_t x = m_geoTag / 10000;
  size_t y = m_geoTag % 10000;

  //std::cout << "node(" << x << ", " << y << ") sd = " << sd << std::endl;
  //std::cout << "node(" << x << ", " << y << ") t_fw_max = " << t_fw_max << std::endl;
  //std::cout << "node(" << x << ", " << y << ") t_fw = " << t_fw << std::endl;

  shared_ptr<sit::Entry> sitEntry = m_sit.insert(interest);
  BOOST_ASSERT(sitEntry != nullptr);
  sitEntry->m_scheduleInterestTimer = scheduler::schedule(time::milliseconds(t_fw),
    bind(&Forwarder::onSitSchedulerTimeout, this, ref(inFace), sitEntry, ref(interest), pitEntry));
}

void
Forwarder::onSitSchedulerTimeout(const Face& inFace, const shared_ptr<sit::Entry>& sitEntry,
                                 Interest& interest, const shared_ptr<pit::Entry>& pitEntry)
{
  NFD_LOG_DEBUG("node(" << m_geoTag << ")" << "onSitSchedulerTimeout interest=" << interest.getName());
  //scheduler::cancel(sitEntry->m_scheduleInterestTimer);
  m_sit.erase(sitEntry.get());

  // pit may have been deleted
  name_tree::Entry* nte = m_nameTree.getEntry(*pitEntry);
  if (nte == nullptr) return;

  // modify the interest [lastGeoTag]
  interest.setLastGeo(m_geoTag);

  // dispatch to strategy: after incoming Interest
  // using multicast here!
  this->dispatchToStrategy(*pitEntry,
    [&] (fw::Strategy& strategy) { strategy.afterReceiveInterest(inFace, interest, pitEntry); });
  NFD_LOG_DEBUG("node(" << m_geoTag << ")" << "onSitSchedulerTimeout finish!");
}

void
Forwarder::onGeoContentStoreHit(const Face& inFace, const shared_ptr<pit::Entry>& pitEntry,
                                const Interest& interest_, const Data& data,
                                Interest& interest)
{
  NFD_LOG_DEBUG("node(" << m_geoTag << ")" << "onGeoContentStoreHit interest=" << interest.getName());

  // no beforeStrategyInterest
  // and no need for creating PIT entry

  data.setTag(make_shared<lp::IncomingFaceIdTag>(face::FACEID_CONTENT_STORE));

  // Question here!!!!
  //if (m_sd.find(data) != nullptr) return;
  std::shared_ptr<sd::Entry> sdEntryExist = m_sd.find(data.getName());
  if (sdEntryExist != nullptr) {
    if (sdEntryExist->isTimeOut()) return;
    this->geoOnInterestFinalize(pitEntry);
    return;
  }

  uint64_t t_dataout = getRandomNumber(0, 100);
  shared_ptr<sd::Entry> sdEntry = m_sd.insert(data);
  BOOST_ASSERT(sdEntry != nullptr);
  sdEntry->m_scheduleDataTimer = scheduler::schedule(time::milliseconds(t_dataout), 
    bind(&Forwarder::onSdSchedulerTimeout, this, ref(inFace), cref(data), sdEntry, pitEntry));
}

void
Forwarder::onSdSchedulerTimeout(const Face& inFace, const Data& data,
                                const shared_ptr<sd::Entry>& sdEntry,
                                const shared_ptr<pit::Entry>& pitEntry)
{
  NFD_LOG_DEBUG("node(" << m_geoTag << ")" << "onSdSchedulerTimeout data=" << data.getName());
  BOOST_ASSERT(sdEntry != nullptr);
  sdEntry->setTimeOut();
  //scheduler::cancel(sdEntry->m_scheduleDataTimer);
  // delete sdEntry
  m_sd.erase(sdEntry.get());

  // pit may have been deleted
  name_tree::Entry* nte = m_nameTree.getEntry(*pitEntry);
  if (nte == nullptr) return;

  // set PIT straggler timer
  this->setStragglerTimer(pitEntry, true, data.getFreshnessPeriod());

  // no need to set PIT straggler timer
  // goto outgoing Data pipeline
  this->onOutgoingData(data, *const_pointer_cast<Face>(inFace.shared_from_this()));
}

void
Forwarder::onIncomingGeoData(Face& inFace, const Data& data)
{
  // receive Data
  NFD_LOG_DEBUG("node(" << m_geoTag << ")" << "onIncomingGeoData face=" << inFace.getId() << " data=" << data.getName());
  data.setTag(make_shared<lp::IncomingFaceIdTag>(inFace.getId()));
  ++m_counters.nInData;

  // /localhost scope control
  bool isViolatingLocalhost = inFace.getScope() == ndn::nfd::FACE_SCOPE_NON_LOCAL &&
                              scope_prefix::LOCALHOST.isPrefixOf(data.getName());
  if (isViolatingLocalhost) {
    NFD_LOG_DEBUG("onIncomingGeoData face=" << inFace.getId() <<
                  " data=" << data.getName() << " violates /localhost");
    // (drop)
    return;
  }

  // PIT match
  pit::DataMatchResult pitMatches = m_pit.findAllDataMatches(data);
  if (pitMatches.begin() == pitMatches.end()) {
    // goto Data unsolicited pipeline
    this->onDataUnsolicited(inFace, data);
    return;
  }

  // If it is scheduled, then remove the scheduled transmission, remove PIT entry, and stop processing.
  std::shared_ptr<sd::Entry> sdEntry = m_sd.find(data.getName());
  if (sdEntry != nullptr) {
    if (sdEntry->isTimeOut()) return;
    scheduler::cancel(sdEntry->m_scheduleDataTimer);

    for (const shared_ptr<pit::Entry>& pitEntry : pitMatches) {
      NFD_LOG_DEBUG("remove PitEntries because of scheduled data");
      this->geoOnInterestFinalize(pitEntry);
      /*
      this->cancelUnsatisfyAndStragglerTimer(*pitEntry);
      // Dead Nonce List insert if necessary (for out-record of inFace)
      //this->insertDeadNonceList(*pitEntry, true, data.getFreshnessPeriod(), &inFace);

      // mark PIT satisfied
      pitEntry->clearInRecords();
      pitEntry->deleteOutRecord(inFace);

      m_pit.erase(pitEntry.get());
      */
    }
    m_sd.erase(sdEntry.get());
    return;
  }

  for (const shared_ptr<pit::Entry>& pitEntry : pitMatches) {
    // cancel unsatisfy & straggler timer
    this->cancelUnsatisfyAndStragglerTimer(*pitEntry);
  }

  uint64_t t_dataout = getRandomNumber(0, 100);
  sdEntry = m_sd.insert(data);
  BOOST_ASSERT(sdEntry != nullptr);
  sdEntry->m_scheduleDataTimer = scheduler::schedule(time::milliseconds(t_dataout), 
    bind(&Forwarder::onSdSchedulerTimeout2, this, ref(inFace), cref(data), sdEntry, pitMatches));
}

void
Forwarder::onSdSchedulerTimeout2(Face& inFace, const Data& data,
                                 shared_ptr<sd::Entry>& sdEntry, pit::DataMatchResult& pitMatches) 
{
  NFD_LOG_DEBUG("node(" << m_geoTag << ")" << "onSdSchedulerTimeout2 data=" << data.getName());
  sdEntry->setTimeOut();
  BOOST_ASSERT(sdEntry != nullptr);

  shared_ptr<Data> dataCopyWithoutTag = make_shared<Data>(data);
  dataCopyWithoutTag->removeTag<lp::HopCountTag>();

  // CS insert
  if (m_csFromNdnSim == nullptr)
    m_cs.insert(*dataCopyWithoutTag);
  else
    m_csFromNdnSim->Add(dataCopyWithoutTag);

  // send out the data
  std::set<Face*> pendingDownstreams;
  // foreach PitEntry
  auto now = time::steady_clock::now();
  for (const shared_ptr<pit::Entry>& pitEntry : pitMatches) {
    // in case the pit has been deleted
    name_tree::Entry* nte = m_nameTree.getEntry(*pitEntry);
    if (nte == nullptr) continue;
    // remember pending downstreams
    for (const pit::InRecord& inRecord : pitEntry->getInRecords()) {
      if (inRecord.getExpiry() > now) {
        pendingDownstreams.insert(&inRecord.getFace());
      }
    }

    // invoke PIT satisfy callback
    beforeSatisfyInterest(*pitEntry, inFace, data);
    this->dispatchToStrategy(*pitEntry,
      [&] (fw::Strategy& strategy) { strategy.beforeSatisfyInterest(pitEntry, inFace, data); });

    // Dead Nonce List insert if necessary (for out-record of inFace)
    this->insertDeadNonceList(*pitEntry, true, data.getFreshnessPeriod(), &inFace);
    //this->geoInsertDeadNonceList(*pitEntry, &inFace);

    // mark PIT satisfied
    pitEntry->clearInRecords();
    pitEntry->deleteOutRecord(inFace);

    // set PIT straggler timer

    this->setStragglerTimer(pitEntry, true, data.getFreshnessPeriod());
  }
  if (pendingDownstreams.empty()) {
    NFD_LOG_DEBUG("PitEntries all deleted by others!");
    m_sd.erase(sdEntry.get());
    return;
  }

  // foreach pending downstream
  for (Face* pendingDownstream : pendingDownstreams) {
    // because of the wifi environment
    /*
    if (pendingDownstream == &inFace) {
      continue;
    }
    */
    // goto outgoing Data pipeline
    this->onOutgoingData(data, *pendingDownstream);
  }

  // remove sdEntry
  m_sd.erase(sdEntry.get());
  
  //std::cout << "node(" << m_geoTag << ")" << "onSdSchedulerTimeout2 receive data" << std::endl;
}

//////////////////////////////////////////////////////////////////////////////////////
/* @brief A sleeping mode schedule based on information of pit&cs                   //
/* sleepSignal will not be forwarded any more. In other words, only in Tx range     //
*/////////////////////////////////////////////////////////////////////////////////////
void 
Forwarder::timelineStart(const time::steady_clock::TimePoint& timelineStart)
{
  auto now = time::steady_clock::now();
  auto timelineStartFromNow = timelineStart - now;
  NFD_LOG_DEBUG("first timeline schedule from now = " << timelineStartFromNow);
  scheduler::schedule(timelineStartFromNow,
    bind(&Forwarder::timelineSchedule, this));
}

void
Forwarder::onIncomingSleepSignal(Face& inFace, const Interest& interest)
{
  //std::cout << "node(" << m_geoTag << ")" << "onIncomingSleepSignal" << std::endl;
  if (!m_sleepSignalTimeOut) {
    m_otherTimeOut++;
    if (m_otherTimeOut >= 1) {
      scheduler::cancel(m_sleepSignalTimer);
      return;
    }
  }
}

void 
Forwarder::timelineSchedule() 
{
  NFD_LOG_DEBUG("entering timelineSchedule!");
  BOOST_ASSERT(is_sleeping == false);
  /*
  if (is_sleeping == true) {
    NFD_LOG_DEBUG("Timeline schedule wrong! node is still sleeping!");
    scheduer::cancel(m_sleepTimer);
  }
  */
  setSleepSignalTimer();
  m_timelineTimer = scheduler::schedule(time::seconds(100), 
    bind(&Forwarder::timelineSchedule, this));
}

void 
Forwarder::setSleepSignalTimer()
{
  BOOST_ASSERT(is_sleeping == false);
  size_t pitSize = m_pit.size();
  size_t csSize = m_cs.size();
  size_t sitSize = m_sit.size();
  size_t sdSize = m_sd.size();
  //std::cout << "node(" << m_geoTag << ") infoNum = " << pitSize + csSize + sitSize + sdSize << std::endl;
  // N = alpha * pitSize + belta * csSize
  size_t min;
  size_t max;
  if (pitSize > csSize) {
    min = 100 * csSize;
    max = 100 * pitSize;
  }
  else {
    min = 100 * pitSize;
    max = 100 * csSize;
  }
  //size_t N = 100 * pitSize + 100 * csSize;
  uint64_t t_sleepSignal = getRandomNumber(min, max);
  // E = energyLeft
  t_sleepSignal = infoNum;
  std::cout << "node(" << m_geoTag << ") will send the sleep signal after " << t_sleepSignal << std::endl;
  m_sleepSignalTimer = scheduler::schedule(time::milliseconds(t_sleepSignal),
    bind(&Forwarder::sendSleepSignal, this));
}

void
Forwarder::sendSleepSignal()
{
  //std::cout << "node(" << m_geoTag << "send sleep signal!" << std::endl;
  auto interest_name = Name("/ndn/sleep_signal");
  Interest sleepSignal(interest_name);
  const fib::Entry& fibEntry = m_fib.findLongestPrefixMatch(sleepSignal.getName());
  const fib::NextHopList& nexthops = fibEntry.getNextHops();
  for (fib::NextHopList::const_iterator it = nexthops.begin(); it != nexthops.end(); ++it) {
    Face& outFace = it->getFace();  
    outFace.sendInterest(sleepSignal);
  }
  setSleepTimer();
}

void
Forwarder::setSleepTimer()
{
  BOOST_ASSERT(is_sleeping == false);
  is_sleeping = true;
  // TODO
  // implement the sleeping schedule
  //std::cout << "node(" << m_geoTag << ") go to sleep" << std::endl;
  std::cout << m_geoTag / 10000 << "," << m_geoTag % 10000 << std::endl;
  uint64_t sleepTime = 50;
  m_sleepTimer = scheduler::schedule(time::seconds(sleepTime),
    bind(&Forwarder::wakeUp, this));
}

void 
Forwarder::wakeUp()
{
  BOOST_ASSERT(is_sleeping == true);
  is_sleeping = false;
}

} // namespace nfd