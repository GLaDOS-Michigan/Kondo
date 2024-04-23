include "spec.dfy"

module ShardedKVBatchedProof {
import opened Types
import opened UtilitiesLibrary
import opened System
import opened Obligations


// Protocol bundle
ghost predicate ProtocolInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && true
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ProtocolInv(c, v)
  && Safety(c, v)
}


/***************************************************************************************
*                                Top-level Obligations                                 *
***************************************************************************************/


lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{}

} // end module ShardedKVBatchedProof