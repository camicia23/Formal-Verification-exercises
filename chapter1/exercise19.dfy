//#title IsSeqSorted
//#desc Build an entire imperative loop method implementation with loop
//#desc invariants.

predicate IsSorted(intseq:seq<int>) {
  forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

method IsSeqSorted(intSeq:seq<int>) returns (issorted:bool)
  ensures issorted <==> IsSorted(intSeq[..])
{
  /*{*/
  issorted := true;

  for sup := 0 to |intSeq|
    invariant issorted <==> forall i, j | 0 <= i < j < sup :: intSeq[i] <= intSeq[j]
  {
    var stillSorted:bool := forall i | 0 <= i < sup :: intSeq[i] <= intSeq[sup];
    if !stillSorted { issorted := false; }
  }
  /*}*/
}
