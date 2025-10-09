//#title Midterm Project
//#desc Build a distributed lock server. Define how a host implements your
//#desc protocol in host.v.dfy; write your safety spec and proof here.

// This challenge differs from LockServer (from chapters 03 and 04) in two
// ways. First, there is no central server that coordinates the activity.
// Second, the hosts can communicate only via asynchronous messages; a single
// state machine transition cannot simultaneously read or update the state of
// two hosts.
//
// To guard against duplicate messages, the nodes associate a monotonically
// increasing epoch number with the lock. Initially, node 0 holds the lock and
// its epoch number is 1, while all other nodes with an epoch of 0 (and not
// holding the lock). A node that holds the lock can “grant” it to another
// node by sending them a “Grant” message which has an epoch number that is
// greater than the node's epoch number. A node that receives such a message
// will become the new holder and will set its epoch number to the message’s
// epoch number.

// You'll first need to modify 'host.v.dfy' to define the protocol message
// format and the host behavior.
// Then come back here to define the safety condition and prove that the
// distributed system made from that protocol maintains it.

include "distributed_system.t.dfy"
//#extract distributed_system.t.template solution distributed_system.t.dfy

module SafetySpec {
  import opened HostIdentifiers
  import DistributedSystem

  // Define this predicate to be true if idx is a valid host ID and that host's
  // Variables indicates that it holds the lock.
  ghost predicate HostHoldsLock(c:DistributedSystem.Constants, v:DistributedSystem.Variables, idx: int) {
    && v.WF(c)
    /*{*/
    && 0 <= idx < |v.hosts|
    && v.hosts[idx].ownLock
    /*}*/
  }

  // No two hosts think they hold the lock simultaneously.
  ghost predicate Safety(c:DistributedSystem.Constants, v:DistributedSystem.Variables) {
    /*{*/
    && v.WF(c)
    && forall i:nat, j:nat | i < |v.hosts| && j < |v.hosts| && i != j :: !(v.hosts[i].ownLock && v.hosts[j].ownLock)
    /*}*/
  }
}

module Proof {
  import opened HostIdentifiers
  import Host
  import opened DistributedSystem
  import opened SafetySpec



  // Here's a predicate that will be very useful in constructing invariant conjuncts.
  ghost predicate InFlight(c:Constants, v:Variables, message:Host.Message)
  {
    && v.WF(c)
    && message in v.network.sentMsgs
    /*{*/
    && NetworkMessagesWF(c, v)
    && message.newEpoch > v.hosts[message.receiverId].epoch
    /*}*/
  }

  /*{*/

  ghost predicate InFlight2(c:Constants, v:Variables, message:Host.Message)
  {
    && v.WF(c)
    && message in v.network.sentMsgs
    /*{*/
    && NetworkMessagesWF(c, v)
    && forall i:nat | i < |c.hosts| :: message.newEpoch > v.hosts[i].epoch
    /*}*/
  }

  ghost predicate ExistsInFlight(c:Constants, v:Variables)
    requires NetworkMessagesWF(c, v)
  {
    exists msg:Host.Message | msg in v.network.sentMsgs :: InFlight(c, v, msg)
  }


  ghost predicate NetworkMessagesWF(c:Constants, v:Variables)
  {
    forall msg:Host.Message | msg in v.network.sentMsgs ::
      (
        msg.receiverId < |c.hosts|
      )
  }


  ghost predicate NoMoreThan1InFlight(c:Constants, v:Variables)
    requires NetworkMessagesWF(c, v)
  {
    forall msg1, msg2 | (msg1 in v.network.sentMsgs && msg2 in v.network.sentMsgs && msg1 != msg2) ::
      !(InFlight(c, v, msg1) && InFlight(c, v, msg2))
  }


  ghost predicate HasBiggestEpoch(c:Constants, v:Variables, idx:nat)
    requires v.WF(c)
    requires idx < |c.hosts|
  {
    forall i:nat | i<|c.hosts| && i != idx :: v.hosts[i].epoch < v.hosts[idx].epoch
  }


  ghost predicate SingleOwnsLockDefinition(c:Constants, v:Variables, idx:nat)
    requires v.WF(c)
    requires NetworkMessagesWF(c, v)
    requires idx < |c.hosts|
  {
    v.hosts[idx].ownLock <==> (HasBiggestEpoch(c, v, idx) && !ExistsInFlight(c, v))
  }


  ghost predicate OwnsLockDefinition(c:Constants, v:Variables)
    requires v.WF(c)
    requires NetworkMessagesWF(c, v)
  {
    forall i:nat | i < |c.hosts| :: SingleOwnsLockDefinition(c, v, i)
  }


  ghost predicate InFlightMeansHighestEpoch(c:Constants, v:Variables)
    requires v.WF(c)
    requires NetworkMessagesWF(c, v)
  {
    forall msg:Host.Message | msg in v.network.sentMsgs ::
      (InFlight(c, v, msg) <==> InFlight2(c, v, msg))
  }



  lemma InitImpliesInv(c:Constants, v:Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
    assert |c.hosts|>0 ==> v.hosts[0].ownLock;
  }


  lemma NextPreservesInv(c:Constants, v:Variables, v':Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    assert exists step:Step :: NextStep(c, v, v', step);
    var step:Step :| NextStep(c, v, v', step);
    var msgOps := step.msgOps;
    var id := step.id;

    if (msgOps.recv.Some?) {
      assert msgOps.send.None?;                         // receiving and not sending

      assert Safety(c, v') by {
        assert forall i:nat | i < |c.hosts| :: (SingleOwnsLockDefinition(c, v, i) ==> (ExistsInFlight(c, v) ==> !v.hosts[i].ownLock));
      }
    } else {
      assert msgOps.recv.None? && msgOps.send.Some?;    // sending and not receiving

      assert SingleOwnsLockDefinition(c, v, id);

      assert NoMoreThan1InFlight(c, v');
      assert OwnsLockDefinition(c, v');
      assert InFlightMeansHighestEpoch(c, v');
    }
  }

  /*}*/

  ghost predicate Inv(c: Constants, v:Variables) {
    /*{*/
    && NetworkMessagesWF(c, v)
    && Safety(c, v) // <==> NoMoreThan1Owner(c, v)
    && NoMoreThan1InFlight(c, v)
    && OwnsLockDefinition(c, v)
    && InFlightMeansHighestEpoch(c, v)
    /*}*/
  }

  lemma SafetyProof(c: Constants, v:Variables, v':Variables)
    ensures Init(c, v) ==> Inv(c, v)
    ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
    ensures Inv(c, v) ==> Safety(c, v)
  {
    // Develop any necessary proof here.
    /*{*/
    assert Init(c, v) ==> Inv(c, v) by {
      if Init(c, v) {
        InitImpliesInv(c, v);
      }
    }
    assert Inv(c, v) && Next(c, v, v') ==> Inv(c, v') by {
      if Inv(c, v) && Next(c, v, v') {
        NextPreservesInv(c, v, v');
      }
    }
    /*}*/
  }
}
