//#title Two Phase Commit Model
//#desc Model a distributed protocol using compound state machines.

// Your goal is to model a 2-Phase Commit protocol. You're modeling a single
// instance of the problem -- a designated coordinator, no concurrent
// instances. Furthermore, you may assume there are no coordinator or
// participant failures. This is indeed a fairly simplistic setting, but it's
// still nontrivial, and is a nice example for reasoning about the
// state-machine composition framework.
//
// The input to the algorithm is that each participant has a boolean preference.
// The output is that each participant (and the coordinator) learns a decision value.
//
// 2-Phase Commit Protocol english design doc:
//
// 1, Coordinator sends VOTE-REQ to all participants.
// 2. Each participant i sends back vote_i to coordinator according to its preference.
//   If vote_i=No then i sets decision_i := Abort.
// 3. Coordinator collects votes.
//   If all votes are yes then coordinator sets decision_c := Commit and sends
//   Commit to all participants.
//   Else coordinator sets decision_c := Abort and sends Abort to all
//   participants who voted yes.
// 4. Participants receiving Commit set decision_i := Commit
//
// This file provides a lot of helpful framework. You only need to
// define Types.Message and then fill in the state machine types and actions
// in module CoordinatorHost and module ParticipantHost.
//
// Unlike chapter01, where you could work through each file sequentially,
// WE STRONGLY ENCOURAGE YOU to read the entire file before beginning
// work. Later pieces of the file are helpful, for example by explaining
// the network model you're working in, and by helping you understand
// the role the Constants datatypes play.

include "UtilitiesLibrary.dfy"
include "CommitTypes.dfy"
//#extract CommitTypes.template solution CommitTypes.dfy

module Types {
  import opened UtilitiesLibrary
  import opened CommitTypes

  type HostId = nat

  // Have to define our message datatype so network can refer to it.
  // (There are cleverer ways to parameterize the network module, but
  // we're trying to avoid getting fancy with the Dafny module system.)
  datatype Message =
      /*{*/
    | VOTE_REQ
    | VOTE_ANS(vote:Vote, hostId:HostId)
    | DecisionSet(decision:Decision)
  /*}*/

  // A MessageOps is a "binding variable" used to connect a Host's Next step
  // (what message got received, what got sent?) with the Network (only allow
  // receipt of messages sent prior; record newly-sent messages).
  // Note that both fields are Option. A step predicate can say recv.None?
  // to indicate that it doesn't need to receive a message to occur.
  // It can say send.None? to indicate that it doesn't want to transmit a message.
  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

// There are two host roles in 2PC, Coordinator and Participant. We'll define
// separate state machines for each.
// This state machine defines how a coordinator host should behave: what state
// it records, and what actions it's allowed to take in response to incoming
// messages (or spontaneously by thinking about its existing state).
module CoordinatorHost {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary

  /*{*/
  datatype Constants = Constants(numParticipants:nat)
  /*}*/

  // What relationship must hold between this host's own constants and the
  // structure of the overall group of hosts? It needs to have a correct
  // count of the number of participants.
  ghost predicate ConstantsValidForGroup(c: Constants, participantCount: nat)
  {
    /*{*/
    participantCount == c.numParticipants
    /*}*/
  }

  datatype Variables = Variables(
    decision: Option<Decision>
    /*{*/
  , votes:seq<Option<Vote>>
    /*}*/
  )
  {
    // WF is for a simple condition that relates every valid Variables state
    // to the Constants.
    ghost predicate WF(c: Constants) {
      /*{*/
      && |votes| == c.numParticipants
      && (
           || decision.None?
           || ((forall i:nat | i < c.numParticipants-1 :: votes[i] == Some(Yes)) <==> (decision == Some(Commit)))
         )
      /*}*/
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    /*{*/
    && v.WF(c)
    && v.decision.None?
    && forall i:nat | i < c.numParticipants :: v.votes[i].None?
    /*}*/
  }

  // Protocol steps. Define an action predicate for each step of the protocol
  // that the coordinator is involved in.
  // Hint: it's probably easiest to separate the receipt and recording of
  // incoming votes from detecting that all have arrived and making a decision.
  /*{*/
  ghost predicate SendVOTE_REQ(c:Constants, v:Variables, v':Variables, msgOps:MessageOps) {
    // WF
    && v.WF(c)
    && v'.WF(c)
    // Nothing received
    && msgOps.recv.None?
    // Send vote request
    && msgOps.send.Some?
    && msgOps.send.value.VOTE_REQ?
    // Variables unchanged
    && v' == v
  }

  ghost predicate ReceiveVote(c:Constants, v:Variables, v':Variables, msgOps:MessageOps) {
    // WF
    && v.WF(c)
    && v'.WF(c)
    // Nothing sent
    && msgOps.send.None?
    // Receive vote from someone
    && msgOps.recv.Some?
    && msgOps.recv.value.VOTE_ANS?
    && msgOps.recv.value.hostId < c.numParticipants
    && v.votes[msgOps.recv.value.hostId].None? // not received before
    && v'.votes[msgOps.recv.value.hostId].Some?
    && var rec_id := msgOps.recv.value.hostId;
    var rec_vote := msgOps.recv.value.vote;
    v'.votes == v.votes[rec_id := Some(rec_vote)]
    && v'.decision == v.decision
  }

  ghost predicate MakeSendDecision(c:Constants, v:Variables, v':Variables, msgOps:MessageOps) {
    // WF
    && v.WF(c)
    && v'.WF(c)
    // keep same request_sent_to and votes
    && v'.votes == v.votes
    // everybody voted?
    && (forall i:nat | i < c.numParticipants :: v.votes[i].Some?)

    // nothing received
    && msgOps.recv.None?
    // make decision
    && ((forall i:nat | i < c.numParticipants :: v.votes[i].value.Yes?) <==> (v'.decision == Some(Commit)))
    // send decision
    && msgOps.send.Some?
    && msgOps.send.value.DecisionSet?
    && v'.decision == Some(msgOps.send.value.decision)
    && v.decision.None?    // assume you can decide only once (makes life easier)
  }
  /*}*/

  // JayNF
  datatype Step =
      /*{*/
    | SendVOTE_REQStep
    | ReceiveVoteStep
    | MakeSendDecisionStep
  /*}*/

  // msgOps is a "binding variable" -- the host and the network have to agree
  // on its assignment to make a valid transition. So the host explains what
  // would happen if it could receive a particular message, and the network
  // decides whether such a message is available for receipt.
  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
    /*{*/
    case SendVOTE_REQStep => SendVOTE_REQ(c, v, v', msgOps)
    case ReceiveVoteStep => ReceiveVote(c, v, v', msgOps)
    case MakeSendDecisionStep => MakeSendDecision(c, v, v', msgOps)
    /*}*/
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}

module ParticipantHost {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(hostId: HostId, preference: Vote)

  // What relationship must hold between this host's own constants and the
  // structure of the overall group of hosts? It needs to know its hostId.
  ghost predicate ConstantsValidForGroup(c: Constants, hostId: HostId)
  {
    /*{*/
    c.hostId == hostId
    /*}*/
  }

  datatype Variables = Variables(decision: Option<Decision>)
  {
    ghost predicate WF(c: Constants) {
      /*{*/
      c.preference.No? ==> !(decision.Some? && decision.value.Commit?)
      /*}*/
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    /*{*/
    && v.WF(c)
    && v.decision.None?
    /*}*/
  }

  // Protocol steps. Define an action predicate for each step of the protocol
  // that participant can take.
  /*{*/
  ghost predicate SendVote(c:Constants, v:Variables, v':Variables, msgOps:MessageOps) {
    // WF
    && v.WF(c)
    && v'.WF(c)
    // Receive request for vote
    && msgOps.recv.Some?
    && msgOps.recv.value.VOTE_REQ?
    // Send vote
    && msgOps.send.Some?
    && msgOps.send.value.VOTE_ANS?
    && msgOps.send.value == VOTE_ANS(c.preference, c.hostId)
    // v' == v but change decision if vote==No
    && v.decision.None?
    && (c.preference.No? ==> v'.decision.Some? && v'.decision.value.Abort?)
    && (c.preference.Yes? ==> v'.decision.None?)
  }

  ghost predicate ReceiveDecision(c:Constants, v:Variables, v':Variables, msgOps:MessageOps) {
    // WF
    && v.WF(c)
    && v'.WF(c)
    // Not decided yet
    && v.decision.None?
    // Receive decision and update it
    && msgOps.recv.Some?
    && msgOps.recv.value.DecisionSet?
    && v'.decision.Some?
    && v'.decision.value == msgOps.recv.value.decision
    // Not send anything
    && msgOps.send.None?
  }
  /*}*/

  // JayNF
  datatype Step =
      /*{*/
    | SendVoteStep
    | ReceiveDecisionStep
  /*}*/

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
    /*{*/
    case SendVoteStep => SendVote(c, v, v', msgOps)
    case ReceiveDecisionStep => ReceiveDecision(c, v, v', msgOps)
    /*}*/
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}

// We define a generic Host as able to be either of the specific roles.
// This is the ultimate (untrusted) definition of the protocol we're
// trying to verify.
// This definition is given to you to clarify how the two protocol roles above
// are pulled together into the ultimate distributed system.
module Host {
  import opened UtilitiesLibrary
  import opened CommitTypes
  import opened Types
  import CoordinatorHost
  import ParticipantHost

  datatype Constants =
    | CoordinatorConstants(coordinator: CoordinatorHost.Constants)
    | ParticipantConstants(participant: ParticipantHost.Constants)

  datatype Variables =
    | CoordinatorVariables(coordinator: CoordinatorHost.Variables)
    | ParticipantVariables(participant: ParticipantHost.Variables)
  {
    ghost predicate WF(c: Constants) {
      && (CoordinatorVariables? <==> c.CoordinatorConstants?) // types of c & v agree
      // subtype WF satisfied
      && (match c
          case CoordinatorConstants(_) => coordinator.WF(c.coordinator)
          case ParticipantConstants(_) => participant.WF(c.participant)
         )
    }
  }

  // What property must be true of any group of hosts to run the protocol?
  // Generic DistributedSystem module calls back into this predicate to ensure
  // that it has a well-formed *group* of hosts.
  ghost predicate GroupWFConstants(grp_c: seq<Constants>)
  {
    // There must at least be a coordinator
    && 0 < |grp_c|
    // Last host is a coordinator
    && Last(grp_c).CoordinatorConstants?
    // All the others are participants
    && (forall hostid:HostId | hostid < |grp_c|-1 :: grp_c[hostid].ParticipantConstants?)
    // The coordinator's constants must correctly account for the number of participants
    && CoordinatorHost.ConstantsValidForGroup(Last(grp_c).coordinator, |grp_c|-1)
    // The participants's constants must match their group positions.
    // (Actually, they just need to be distinct from one another so we get
    // non-conflicting votes, but this is an easy way to express that property.)
    && (forall hostid:HostId | hostid < |grp_c|-1
          :: ParticipantHost.ConstantsValidForGroup(grp_c[hostid].participant, hostid))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall hostid:HostId | hostid < |grp_c| :: grp_v[hostid].WF(grp_c[hostid]))
  }

  // Generic DistributedSystem module calls back into this predicate to give
  // the protocol an opportunity to set up constraints across the various
  // hosts.  Protocol requires one coordinator and the rest participants;
  // coordinator must know how many participants, and participants must know
  // own ids.
  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    // constants & variables are well-formed (same number of host slots as constants expect)
    && GroupWF(grp_c, grp_v)
    // Coordinator is initialized to know about the N-1 participants.
    && CoordinatorHost.Init(Last(grp_c).coordinator, Last(grp_v).coordinator)
    // Participants initted with their ids.
    && (forall hostid:HostId | hostid < |grp_c|-1 ::
          ParticipantHost.Init(grp_c[hostid].participant, grp_v[hostid].participant)
       )
  }

  // Dispatch Next to appropriate underlying implementation.
  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && (v'.CoordinatorVariables? <==> v.CoordinatorVariables?)
    && (match c
        case CoordinatorConstants(_) => CoordinatorHost.Next(c.coordinator, v.coordinator, v'.coordinator, msgOps)
        case ParticipantConstants(_) => ParticipantHost.Next(c.participant, v.participant, v'.participant, msgOps)
       )
  }
}

// The (trusted) model of the environment: There is a network that can only deliver
// messages that some Host (running the protocol) has sent, but once sent, messages
// can be delivered repeatedly and in any order.
// This definition is given to you because it's a common assumption you can
// reuse. Someday you might decide to assume a different network model (e.g.
// reliable or at-most-once delivery), but this is a good place to start.
module Network {
  import opened CommitTypes
  import opened Types

  datatype Constants = Constants  // no constants for network

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs ==
       v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}

// The (trusted) model of the distributed system: hosts don't share memory. Each
// takes its steps independently, interleaved in nondeterministic order with others.
// They only communicate through the network, and obey the communication model
// established by the Network model.
// This is given to you; it can be reused for just about any shared-nothing-concurrency
// protocol model.
module DistributedSystem {
  import opened UtilitiesLibrary
  import opened CommitTypes
  import opened Types
  import Network
  import Host
  import CoordinatorHost
  import ParticipantHost

  datatype Constants = Constants(
    hosts: seq<Host.Constants>,
    network: Network.Constants)
  {
    ghost predicate WF() {
      Host.GroupWFConstants(hosts)
    }
    ghost predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hosts, v.hosts)
    && Network.Init(c.network, v.network)
  }

  ghost predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostId(hostid)
    && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
  }

  // JayNF is pretty simple as there's only a single action disjunct
  datatype Step =
    | HostActionStep(hostid: HostId, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && HostAction(c, v, v', step.hostid, step.msgOps)
    // network agrees recv has been sent and records sent
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }

  ghost function GetDecisionForHost(hv: Host.Variables) : Option<Decision>
  {
    match hv
    case CoordinatorVariables(coordinator) => coordinator.decision
    case ParticipantVariables(participant) => participant.decision
  }


  // Convince us that your model does something
  lemma PseudoLiveness(c: Constants) returns (behavior: seq<Variables>)
    requires c.WF()
    requires |c.hosts| == 2 // There's exactly one voting participant...
    requires c.hosts[0].participant.preference.Yes? // ... who wants a Yes.
    requires c.hosts[1].coordinator.numParticipants == 1 // I had to add it outside of /*{*/.../*}*/ to make it a requires
    // Exhibit a behavior that satisfies your state machine...
    ensures 0 < |behavior|
    ensures Init(c, behavior[0])
    ensures forall i:nat | i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1])
    // ...and all the participants arrive at a decision.
    ensures Last(behavior).WF(c)
    ensures forall hostid:HostId | c.ValidHostId(hostid)
              :: GetDecisionForHost(Last(behavior).hosts[hostid]) == Some(Commit)
  {
    /*{*/

    // 0. Initial state
    var partHostVar0:ParticipantHost.Variables := ParticipantHost.Variables(None);
    var hostVar0:Host.Variables := Host.ParticipantVariables(partHostVar0);
    var coordHostVar1:CoordinatorHost.Variables := CoordinatorHost.Variables(None, [None]);
    var hostVar1:Host.Variables := Host.CoordinatorVariables(coordHostVar1);
    var hosts := [hostVar0, hostVar1];

    var sentMsgs:set<Message> := {};
    var network := Network.Variables(sentMsgs);

    var newBehavior := Variables(hosts, network);
    behavior := [newBehavior];


    // 1. Coordinator sends request
    var msg:Message := VOTE_REQ;
    sentMsgs := sentMsgs + {msg};
    network := Network.Variables(sentMsgs);

    newBehavior := Variables(hosts, network);
    behavior := behavior + [newBehavior];


    // 2. Participant receives request and sends back vote
    msg := VOTE_ANS(Yes, 0);
    sentMsgs := sentMsgs + {msg};
    network := Network.Variables(sentMsgs);

    newBehavior := Variables(hosts, network);
    behavior := behavior + [newBehavior];


    // 3. Coordinator receives vote
    coordHostVar1 := CoordinatorHost.Variables(None, [Some(Yes)]);
    hostVar1 := Host.CoordinatorVariables(coordHostVar1);
    hosts := [hosts[0], hostVar1];

    newBehavior := Variables(hosts, network);
    behavior := behavior + [newBehavior];


    // 4. Coordinator chooses and sends decision
    coordHostVar1 := CoordinatorHost.Variables(Some(Commit), [Some(Yes)]);
    hostVar1 := Host.CoordinatorVariables(coordHostVar1);
    hosts := [hosts[0], hostVar1];

    msg := DecisionSet(Commit);
    sentMsgs := sentMsgs + {msg};
    network := Network.Variables(sentMsgs);

    newBehavior := Variables(hosts, network);
    behavior := behavior + [newBehavior];


    // 5. Participant receives decision
    partHostVar0 := ParticipantHost.Variables(Some(Commit));
    hostVar0 := Host.ParticipantVariables(partHostVar0);
    hosts := [hostVar0, hosts[1]];


    newBehavior := Variables(hosts, network);
    behavior := behavior + [newBehavior];



    /////////////
    // PROOFS
    /////////////

    // 0 -> 1
    var msgOps:MessageOps := MessageOps(None, Some(VOTE_REQ));
    var stepCoord:CoordinatorHost.Step := CoordinatorHost.SendVOTE_REQStep;
    assert CoordinatorHost.NextStep(c.hosts[1].coordinator, behavior[0].hosts[1].coordinator, behavior[1].hosts[1].coordinator, stepCoord, msgOps);
    var stepHost:Step := HostActionStep(1, msgOps);
    assert NextStep(c, behavior[0], behavior[1], stepHost);

    // Proof 1->2
    msgOps := MessageOps(Some(VOTE_REQ), Some(VOTE_ANS(Yes, 0)));
    var stepPart:ParticipantHost.Step := ParticipantHost.SendVoteStep;
    assert ParticipantHost.NextStep(c.hosts[0].participant, behavior[1].hosts[0].participant, behavior[2].hosts[0].participant, stepPart, msgOps);
    stepHost := HostActionStep(0, msgOps);
    assert NextStep(c, behavior[1], behavior[2], stepHost);

    // Proof 2->3
    msgOps := MessageOps(Some(VOTE_ANS(Yes, 0)), None);
    stepCoord := CoordinatorHost.ReceiveVoteStep;
    assert CoordinatorHost.NextStep(c.hosts[1].coordinator, behavior[2].hosts[1].coordinator, behavior[3].hosts[1].coordinator, stepCoord, msgOps);
    stepHost := HostActionStep(1, msgOps);
    assert NextStep(c, behavior[2], behavior[3], stepHost);

    // Proof 3->4
    msgOps := MessageOps(None, Some(DecisionSet(Commit)));
    stepCoord := CoordinatorHost.MakeSendDecisionStep;
    assert CoordinatorHost.NextStep(c.hosts[1].coordinator, behavior[3].hosts[1].coordinator, behavior[4].hosts[1].coordinator, stepCoord, msgOps);
    stepHost := HostActionStep(1, msgOps);
    assert NextStep(c, behavior[3], behavior[4], stepHost);

    // Proof 4->5
    msgOps := MessageOps(Some(DecisionSet(Commit)), None);
    stepPart := ParticipantHost.ReceiveDecisionStep;
    assert ParticipantHost.NextStep(c.hosts[0].participant, behavior[4].hosts[0].participant, behavior[5].hosts[0].participant, stepPart, msgOps);
    stepHost := HostActionStep(0, msgOps);
    assert NextStep(c, behavior[4], behavior[5], stepHost);

    /*}*/
  }
}

