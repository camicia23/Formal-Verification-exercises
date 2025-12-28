//#title Two Phase Commit Safety Proof
//#desc Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "exercise02.dfy"
//#extract exercise02.template solution exercise02.dfy

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  /*{*/


  ghost predicate YesDontDecideBeforeDecisionMsg(c:Constants, v:Variables)
    requires v.WF(c)
  {
    !(exists sntMsg | sntMsg in v.network.sentMsgs :: sntMsg.DecisionSet?) ==>
      (forall i:nat | i < |v.hosts|-1 :: c.hosts[i].participant.preference.Yes? ==> v.hosts[i].participant.decision.None?)

  }

  // EquivalentAC1 ==> SafetyAC1
  // Basically all participants choose the same as coordinator
  ghost predicate EquivalentAC1(c:Constants, v:Variables)
    requires v.WF(c)
    requires Last(v.hosts).CoordinatorVariables?
    requires forall i:nat | i < |v.hosts|-1 :: v.hosts[i].ParticipantVariables?
  {
    if Last(v.hosts).coordinator.decision.None?
    then (forall i:nat | i < |v.hosts|-1 :: v.hosts[i].participant.decision.Some? ==> v.hosts[i].participant.decision == Some(Abort))
    else (forall i:nat | i < |v.hosts|-1 :: v.hosts[i].participant.decision.Some? ==> v.hosts[i].participant.decision == Last(v.hosts).coordinator.decision)
  }



  // What coordinator has as votes corresponds to the vote messages
  ghost predicate CoordinatorVotesAgreesWithVotesMsgs(c:Constants, v:Variables)
    requires v.WF(c)
  {
    forall i:nat | i < |v.hosts|-1 :: (Last(v.hosts).coordinator.votes[i].Some? ==>
                                         (
                                           && (exists sntMsg | sntMsg in v.network.sentMsgs :: sntMsg == VOTE_ANS(Last(v.hosts).coordinator.votes[i].value, i))
                                           && (forall sntMsg | sntMsg in v.network.sentMsgs && sntMsg.VOTE_ANS? :: (
                                                                                                                     || !(sntMsg.hostId == i)
                                                                                                                     || sntMsg.vote == Last(v.hosts).coordinator.votes[i].value
                                                                                                                   ))
                                         )

                                      )
  }

  ghost predicate FinalDecisionMsgAgreesWithHost(c:Constants, v:Variables)
    requires v.WF(c)
  {
    forall sntMsg | sntMsg in v.network.sentMsgs && sntMsg.DecisionSet? ::
      Some(sntMsg.decision) == Last(v.hosts).coordinator.decision
  }

  /*}*/
  // This is a conjunct of the inductive invariant, indicating that the messages carrying
  // decisions should reflect the votes of the participants as relayed to the coordinator
  ghost predicate DecisionMsgsAgreeWithDecision(c: Constants, v: Variables)
    requires v.WF(c)
  {
    /*{*/
    forall sntMsg | sntMsg in v.network.sentMsgs && sntMsg.VOTE_ANS? ::
      && c.ValidHostId(sntMsg.hostId)              // potresti anche solo dire sntMsg.hostId < |hosts|-1
      && c.hosts[sntMsg.hostId].ParticipantConstants?
      && c.hosts[sntMsg.hostId].participant.preference == sntMsg.vote

    /*}*/
  }

  ghost predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    /*{*/
    && YesDontDecideBeforeDecisionMsg(c, v)
    && CoordinatorVotesAgreesWithVotesMsgs(c, v)
    && FinalDecisionMsgAgreesWithHost(c, v)
    /*}*/
    // We give you the blueprint for one invariant to get you started...
    && DecisionMsgsAgreeWithDecision(c, v)
    // ...but you'll need more.
    && Safety(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
    /*{*/
    /*}*/
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    /*{*/
    assert YesDontDecideBeforeDecisionMsg(c, v);
    assert FinalDecisionMsgAgreesWithHost(c, v);
    assert DecisionMsgsAgreeWithDecision(c, v);
    assert EquivalentAC1(c, v);
    assert SafetyAC1(c, v);
    assert SafetyAC3(c, v);
    assert SafetyAC4(c, v);



    assert YesDontDecideBeforeDecisionMsg(c, v');
    assert FinalDecisionMsgAgreesWithHost(c, v');
    assert DecisionMsgsAgreeWithDecision(c, v');
    assert CoordinatorVotesAgreesWithVotesMsgs(c, v');


    // SafetyAC1


    assert exists step:Step :: NextStep(c, v, v', step);
    var step :| NextStep(c, v, v', step);
    assert HostAction(c, v, v', step.hostid, step.msgOps);
    assert Host.Next(c.hosts[step.hostid], v.hosts[step.hostid], v'.hosts[step.hostid], step.msgOps);
    assert Network.Next(c.network, v.network, v'.network, step.msgOps);

    if (step.hostid == |c.hosts|-1) {
      // NEXT FOR COORDINATOR

      // assert CoordinatorHost.Next(c.hosts[step.hostid].coordinator, v.hosts[step.hostid].coordinator, v'.hosts[step.hostid].coordinator, step.msgOps);
      assert exists stepCoord:CoordinatorHost.Step :: CoordinatorHost.NextStep(c.hosts[step.hostid].coordinator, v.hosts[step.hostid].coordinator, v'.hosts[step.hostid].coordinator, stepCoord, step.msgOps);
      var stepCoord :| CoordinatorHost.NextStep(c.hosts[step.hostid].coordinator, v.hosts[step.hostid].coordinator, v'.hosts[step.hostid].coordinator, stepCoord, step.msgOps);

      match stepCoord
      case SendVOTE_REQStep =>        // SIMPLY SENDING VOTE REQUEST
        assert SafetyAC1(c, v');
      case ReceiveVoteStep =>         // RECEIVING A VOTE
        assert SafetyAC1(c, v');
      case MakeSendDecisionStep => {  // MAKE AND SEND DECISION

        // SO COORDINATOR HAS DECIDED:
        if(Last(v'.hosts).coordinator.decision == Some(Commit)) {         // TO COMMIT:

          forall i:nat | i < |v'.hosts|-1
            ensures (exists sntMsg | sntMsg in v'.network.sentMsgs :: sntMsg == VOTE_ANS(Yes, i))
          {
            assert (exists sntMsg | sntMsg in v'.network.sentMsgs ::
                      sntMsg == VOTE_ANS(Last(v'.hosts).coordinator.votes[i].value, i));
            assert Last(v'.hosts).coordinator.votes[i].value == Yes;

            var sntMsgWitness :|
              sntMsgWitness in v'.network.sentMsgs &&
              sntMsgWitness == VOTE_ANS(Last(v'.hosts).coordinator.votes[i].value, i);

            assert sntMsgWitness == VOTE_ANS(Yes, i);
          }

          forall i:nat | i < |v'.hosts|-1
            ensures c.hosts[i].participant.preference.Yes?
          {
            assert DecisionMsgsAgreeWithDecision(c, v');
            assert exists sntMsg | sntMsg in v'.network.sentMsgs :: sntMsg == VOTE_ANS(Yes, i);
          }

          assert SafetyAC1(c, v');
        } else {          // TO ABORT:
          assert Last(v'.hosts).coordinator.decision.value == Abort;
          assert SafetyAC1(c, v');
        }

        assert SafetyAC1(c, v');
      }

      // SO IF COORDINATOR CHANGING ALL FINE
      assert SafetyAC1(c, v');

    } else {
      // NEXT FOR PARTICIPANT

      // assert ParticipantHost.Next(c.hosts[step.hostid].participant, v.hosts[step.hostid].participant, v'.hosts[step.hostid].participant, step.msgOps);
      assert exists stepPart:ParticipantHost.Step :: ParticipantHost.NextStep(c.hosts[step.hostid].participant, v.hosts[step.hostid].participant, v'.hosts[step.hostid].participant, stepPart, step.msgOps);
      var stepPart :| ParticipantHost.NextStep(c.hosts[step.hostid].participant, v.hosts[step.hostid].participant, v'.hosts[step.hostid].participant, stepPart, step.msgOps);

      match stepPart
      case SendVoteStep => {      // SENDING VOTE

        if(c.hosts[step.hostid].participant.preference.Yes?){   // IF PARTICIPANT VOTED YES
          assert SafetyAC1(c, v');
        } else {                                                // ...OR VOTED NO
          assert v'.hosts[step.hostid].participant.decision == Some(Abort);
          assert Last(v'.hosts).coordinator.votes[step.hostid].None? || Last(v'.hosts).coordinator.votes[step.hostid] == Some(No);

          assert !(Last(v'.hosts).coordinator.decision == Some(Commit));
          assert forall dec:Decision :: dec == Commit || dec == Abort;
          assert Last(v'.hosts).coordinator.decision.None? || Last(v'.hosts).coordinator.decision == Some(Abort);
          assert SafetyAC1(c, v');

        }

        assert SafetyAC1(c, v');
      }
      case ReceiveDecisionStep => {     // RECEIVING THE DECISION
        assert SafetyAC1(c, v');
      }

    }
    assert SafetyAC1(c, v');

    assert SafetyAC3(c, v');
    assert SafetyAC4(c, v');
    /*}*/
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
