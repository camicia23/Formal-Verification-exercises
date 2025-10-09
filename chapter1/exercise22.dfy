//#title Binary Tree Search
//#desc Implement search in a binary tree and prove it works.
//#desc Practice with proof diagnosis.

include "exercise21.dfy"
//#extract exercise21.template solution exercise21.dfy

// This exercise builds on exercise21 (so make sure you have completed
// that one, too). If in doubt about your solution to exercise21, contact
// an instructor during office hours to make sure you're on the right path.

predicate SequenceIsSorted(intseq:seq<int>) {
  forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

lemma SortedTreeMeansSortedSequence(tree:Tree)
  requires IsSortedTree(tree)
  ensures SequenceIsSorted(TreeAsSequence(tree))
{
}

method FindInBinaryTree(tree:Tree, needle:int) returns (found:bool)
  requires IsSortedTree(tree)
  ensures found <==> needle in TreeAsSequence(tree)
{
  /*{*/
  SortedTreeMeansSortedSequence(tree);

  match tree {
    // empty
    case Nil => { return false; }
    case Node(value, left, right) => {

      // it's this value
      if value == needle {
        return true;

        // else it's in left
      } else if needle < value {
        SortedTreeMeansSortedSequence(right);
        found := FindInBinaryTree(left, needle);

        // else it's in right
      } else {
        SortedTreeMeansSortedSequence(left);
        found := FindInBinaryTree(right, needle);
      }
    }
  }
  /*}*/
}
