// User level proofs of application invariants

include "spec.dfy"


module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

// Message Invariant: self inductive
ghost predicate ValidMessages(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs 
  :: match msg 
      case VoteReq(candidate) => c.ValidHostId(candidate)
      case Vote(voter, candidate) => c.ValidHostId(voter)
}

// Message Invariant: self inductive
ghost predicate ReceivedVotesValidity(c: Constants, v: Variables) 
  requires v.WF(c)
{
  forall idx, voter | c.ValidHostId(idx) && voter in v.hosts[idx].receivedVotes 
  :: Vote(voter, idx) in v.network.sentMsgs
}

// Message Invariant: self inductive
// Property of Send
ghost predicate VoteMsgImpliesNominee(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Vote?
  :: v.hosts[msg.voter].nominee == WOSome(msg.candidate)
}

ghost predicate MessageInv(c: Constants, v: Variables) 
{
  && v.WF(c)
  && ValidMessages(c, v)
  && ReceivedVotesValidity(c, v)
  && VoteMsgImpliesNominee(c, v)
}

lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{}

lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{
  assert ValidMessages(c, v');
  assert ReceivedVotesValidity(c, v');
}

}

