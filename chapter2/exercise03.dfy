//#title Merge Sort
//#desc More specification practice.

// Implement a merge sort that guarantees the result is sorted.
// merge() should merge its two sorted inputs into a sorted output.
// merge_sort picks a pivot, recursively merge_sort()s the subsequences,
// and then uses merge() to put them back together. We've provided
// signatures for merge and merge_sort to get you started.

predicate IsSorted(seqint:seq<int>)
{
  forall idx :: 0 <= idx < |seqint|-1 ==> seqint[idx] <= seqint[idx+1]
}

/*{*/

lemma SplittingKeepsMultiset(a:seq<int>, p:nat)
  requires 0 <= p <= |a|
  ensures multiset(a) == multiset(a[..p]) + multiset(a[p..])
{
  assert a == a[..p] + a[p..];
}

/*}*/
method merge_sort(input:seq<int>) returns (output:seq<int>)
  /*{*/
  ensures IsSorted(output)
  ensures multiset(input) == multiset(output)
  /*}*/
{
  /*{*/
  if |input| <= 1 {
    return input;
  }
  var l:nat := |input|/2;
  var outputA := merge_sort(input[..l]);
  var outputB := merge_sort(input[l..]);

  assert input[..l] + input[l..] == input;

  output := merge(outputA, outputB);
  /*}*/
}

method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
  requires IsSorted(seqa)
  requires IsSorted(seqb)
  /*{*/
  ensures multiset(output) == multiset(seqa) + multiset(seqb)
  ensures IsSorted(output)
  /*}*/
{
  /*{*/
  output := [];

  var pa := 0;
  var pb := 0;

  while pa < |seqa| && pb < |seqb|
    invariant 0 <= pa <= |seqa| && 0 <= pb <= |seqb|

    invariant pa>=1 ==> (pa<|seqa| ==> seqa[pa-1] <= seqa[pa]) && (pb<|seqb| ==> seqa[pa-1] <= seqb[pb])
    invariant pb>=1 ==> (pa<|seqa| ==> seqb[pb-1] <= seqa[pa]) && (pb<|seqb| ==> seqb[pb-1] <= seqb[pb])
    invariant |output|==0 || (pa-1>=0 && output[|output|-1] == seqa[pa-1]) || (pb-1>=0 && output[|output|-1] == seqb[pb-1])
    invariant IsSorted(output)

    invariant multiset(output) == multiset(seqa[..pa]) + multiset(seqb[..pb])

    decreases (|seqa| - pa) + (|seqb| - pb)
  {

    if seqa[pa] <= seqb[pb] {
      assert seqa[..pa] + [seqa[pa]] == seqa[..pa+1];
      assert (multiset(output) == multiset(seqa[..pa]) + multiset(seqb[..pb])) ==>
          (multiset(output + [seqa[pa]]) == multiset(seqa[..pa+1]) + multiset(seqb[..pb]));


      output := output + [seqa[pa]];
      pa := pa + 1;
    } else {
      assert seqb[..pb] + [seqb[pb]] == seqb[..pb+1];
      assert (multiset(output) == multiset(seqb[..pb]) + multiset(seqb[..pb])) ==>
          (multiset(output + [seqb[pb]]) == multiset(seqb[..pb+1]) + multiset(seqb[..pb]));

      output := output + [seqb[pb]];
      pb := pb + 1;
    }
  }


  // Dim multiset...
  assert multiset(output) == multiset(seqa[..pa]) + multiset(seqb[..pb]);
  SplittingKeepsMultiset(seqa, pa);
  SplittingKeepsMultiset(seqb, pb);
  assert multiset(output + seqa[pa..] + seqb[pb..]) ==
         multiset(seqa[..pa]) + multiset(seqa[pa..]) + multiset(seqb[..pb]) + multiset(seqb[pb..]);
  // End dim


  // Dim IsSorted...
  assert IsSorted(output + seqa[pa..]);
  assert IsSorted(output + seqb[pb..]);
  // End dim

  output := output + seqa[pa..];
  output := output + seqb[pb..];

  /*}*/
}

