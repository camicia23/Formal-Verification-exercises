include "Network.t.dfy"
//#extract Network.t.template inherit Network.t.dfy
include "Host.v.dfy"
//#extract Host.v.template inherit Host.v.dfy

module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host

  type HostId = Network.HostId

  /*{*/
  datatype Constants = Constants(hostIds: set<HostId>)   // emptyNetworkC: Network.Constants,
  {

    ghost predicate WF() {
      && 0 in hostIds
    }
  }
  datatype Variables = Variables(hosts: map<HostId, Host.Variables>, network: Network.Variables)
  {

    ghost predicate WF(c: Constants) {
      && c.WF()
      && hosts.Keys == c.hostIds
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Network.Init(Network.Constants(), v.network)
    && forall id:nat | id in c.hostIds :: Host.Init(Host.Constants(id), v.hosts[id])
  }

  datatype Step = Step(id:HostId, msgOps:Network.MessageOps)

  ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step:Step, event:Event)
  {
    && v.WF(c)
    && v'.WF(c)
    && var id := step.id;
    && var msgOps := step.msgOps;
    && id in c.hostIds
    && Host.Next(Host.Constants(id), v.hosts[id], v'.hosts[id], msgOps, event)
    && Network.Next(Network.Constants(), v.network, v'.network, msgOps)
    && v'.hosts == v.hosts[id := v'.hosts[id]]
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
  {
    exists step:Step :: NextStep(c, v, v', step, event)
  }
  /*}*/
}