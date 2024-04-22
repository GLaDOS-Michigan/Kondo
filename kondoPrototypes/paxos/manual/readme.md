# Readme

Updating on 7 May 2023 to remove atomic receive-and-send in same step.

Below are old message invariants that are no longer true in this non-atomic setting.
They become application invariants

```dafny
// certified self-inductive
// Acceptor updates its promised ballot based on a Prepare/Propose message carrying 
// that ballot
predicate AcceptorValidPromised(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, b | c.ValidAcceptorIdx(idx) && v.acceptors[idx].promised == Some(b)
  :: (exists m: Message ::
        && (IsPrepareMessage(v, m) || IsProposeMessage(v, m))
        && m.bal == b
    )
}

// certified self-inductive
// Acceptor updates its acceptedVB based on a Propose message carrying that ballot 
// and value, and there is also a corresponding Accept message
predicate AcceptorValidAcceptedVB(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, val, bal | 
    && c.ValidAcceptorIdx(idx) 
    && v.acceptors[idx].acceptedVB == Some(VB(val, bal))
  :: 
    && Propose(bal, val) in v.network.sentMsgs
    && Accept(VB(val, bal), c.acceptorConstants[idx].id) in v.network.sentMsgs
}
```
