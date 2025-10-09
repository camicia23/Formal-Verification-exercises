//#title Sort Specification
//#desc More specification practice.

// You are asked to define the specification (i.e. the postcondition)
// for a sorting method. Note that you are not implementing the method
// itself, just the postcondition; so there is nothing to prove. The
// autograder will check the correctness of your postcondition.
//
// Start by defining the IsSorted() predicate (which should return true
// if the given sequence is sorted). The final postcondition for the
// sort method is SortSpec(), which is currently defined as IsSorted(output),
// though can change that, if needed.

// In the end, the SortSpec predicate will be used as follows:
// method sort(input:seq<int>) returns (output:seq<int>)
//   ensures SortSpec(input, output)
// {
//   ... //body here
// }

predicate IsSorted(seqint:seq<int>)
{
  /*{*/
  forall i,j:nat | 0 <= i < j < |seqint| :: seqint[i] <= seqint[j]
  /*}*/
}

predicate SortSpec(input:seq<int>, output:seq<int>)
{
  /*{*/
  && IsSorted(output)
  && multiset(input) == multiset(output)
  /*}*/
}

