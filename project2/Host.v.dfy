include "UtilitiesLibrary.t.dfy"
include "IMapHelpers.t.dfy"
include "Types.t.dfy"
//#extract Types.t.template inherit Types.t.dfy
include "MessageType.v.dfy"
//#extract MessageType.v.template inherit MessageType.v.dfy
include "Network.t.dfy"
//#extract Network.t.template inherit Network.t.dfy

//
// Your protocol should capture the idea that keys "live" on different hosts
// *and can move around* from host to host. So, in addition to implementing
// client-visible actions as described in AtomicKVSpec, each host should have a way
// to send part of its state to another host, and to receive the corresponding
// message from another sender. (The messages can move a batch of key-value
// pairs, or a single pair at a time; neither is particularly harder than the
// other.)
//
// Obviously, the hosts must be aware of which fraction of the keyspace they
// own at any given time, so that a host doesn't try to service a Get or Put
// request when the "real state" is off at some other host right now.
//
// Initially host 0 should own all the keys.
//
// Don't forget about the helper functions in IMapHelpers.t.dfy. They can be
// quite useful!

module Host {
  import opened UtilitiesLibrary
  import opened IMapHelpers
  import opened Types
  import opened MessageType
  import Network

  type HostId = Network.HostId

  /*{*/
  // Replace these definitions with more meaningful ones that capture the operations
  // of a key-value store described above.
  datatype Constants = Constants(hostId:HostId)
  datatype Variables = Variables(
    key_val: imap<int, int>
  )

  ghost predicate Init(c:Constants, v:Variables)
  {
    && if c.hostId == 0
    then v.key_val == ZeroMap()
    else v.key_val == EmptyMap()
  }

  ghost predicate HostGet(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps, key:int, val:int)
  {
    && key in v.key_val
    && val == v.key_val[key]
    && v' == v
    && msgOps.recv.None?
    && msgOps.send.None?
  }

  ghost predicate HostPut(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps, key:int, val:int)
  {
    && key in v.key_val
    && v'.key_val == v.key_val[key := val]
    && msgOps.recv.None?
    && msgOps.send.None?
  }

  ghost predicate HostNoOp(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps)
  {

    || (    // Receive
         && msgOps.send.None?
         && msgOps.recv.Some?
         && var msg := msgOps.recv.value;
         && msg.Message?
         && var imap_recv := imap k | k in msg.payload :: msg.payload[k];
         && v'.key_val == IMapUnionPreferLeft(v.key_val, imap_recv)
       )

    || (    // Send
         && msgOps.recv.None?
         && msgOps.send.Some?
         && var msg := msgOps.send.value;
         && msg.Message?
         && (forall k :: k in msg.payload ==> k in v.key_val)
         && (forall k :: k in msg.payload ==> msg.payload[k] == v.key_val[k])
         && var iset_msg := set k | k in msg.payload;
         && v'.key_val == v.key_val - iset_msg
         //  && v'.key_val == MapRemove(v.key_val, iset_msg)
       )

    || (    // NoOp
         && v' == v
         && msgOps.send.None?
         && msgOps.recv.None?
       )
  }

  ghost predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps, evt:Event)
  {
    match evt {
      case Get(key, val) => HostGet(c, v, v', msgOps, key, val)
      case Put(key, val) => HostPut(c, v, v', msgOps, key, val)
      case NoOp() => HostNoOp(c, v, v', msgOps)
    }
  }
  /*}*/
}
