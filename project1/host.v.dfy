//#title Host protocol
//#desc Define the host state machine here: message type, state machine for executing one
//#desc host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.t.dfy"
//#extract network.t.template solution network.t.dfy

module Host {
  import opened UtilitiesLibrary
  import opened HostIdentifiers
  import Network

  // Define your Message datatype here.
  datatype Message =
    /*{*/
    Grant(newEpoch:nat, receiverId:nat)
  /*}*/

  // Define your Host protocol state machine here.
  datatype Constants = Constants(numHosts: nat, myId:HostId) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    ghost predicate Configure(numHosts: nat, id:HostId) {
      && this.numHosts == numHosts
      && this.myId == id
    }
  }

  datatype Variables = Variables(
    /*{*/
    ownLock:bool, epoch:nat
    /*}*/
  )

  ghost predicate Init(c:Constants, v:Variables) {
    /*{*/
    if c.myId==0
    then (v.epoch==1 && v.ownLock==true)
    else (v.epoch==0 && v.ownLock==false)
    /*}*/
  }

  /*{*/
  ghost predicate GiveGrant(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    && v.ownLock == true
    && v'.ownLock == false
    && v.epoch == v'.epoch

    && msgOps.recv.None?
    && msgOps.send.Some?
    && msgOps.send.value.Grant?
    && msgOps.send.value.newEpoch > v.epoch
    && msgOps.send.value.receiverId < c.numHosts
  }

  ghost predicate ReceiveGrant(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    && v.ownLock == false
    && v'.ownLock == true
    && v'.epoch > v.epoch

    && msgOps.send.None?
    && msgOps.recv.Some?
    && msgOps.recv.value.Grant?
    && msgOps.recv.value.newEpoch == v'.epoch
    && msgOps.recv.value.receiverId == c.myId
  }

  /*}*/
  // JayNF
  datatype Step =
      /*{*/
    | GiveGrantStep
    | ReceiveGrantStep
  /*}*/

  ghost predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
    /*{*/
    case GiveGrantStep => GiveGrant(c, v, v', msgOps)
    case ReceiveGrantStep => ReceiveGrant(c, v, v', msgOps)
    /*}*/
  }

  ghost predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
