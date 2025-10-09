//#title Binary Tree Is Sorted
//#desc Prove an implementation meets its spec.
//#desc Practice with proof diagnosis.

include "UtilitiesLibrary.dfy"
import opened UtilitiesLibrary

// Define a Binary Tree and write a method to check if it is sorted

// A binary tree is a tree data structure in which each (internal) node has a value and at
// most two children, which are referred to as the left child and the right child.

/*{*/
// you should define your Tree datatype here.
datatype Tree = Nil | Node(value: int, left: Tree, right: Tree)
/*}*/

// This lemma is here to guide you in defining the tree in a way
// that will help with the rest of the exercise.
lemma DatatypeCheck()
{
  var emptyTree := Nil;
  var littleTree := Node(9, Nil, Nil);
  var biggerTree := Node(10, littleTree, littleTree); // Note: not sorted
}

// You will find the following function method useful. It is meant to express
// the given tree as a sequence.
//
// Note: a function method is just like a ghostfunction, except it
// can be used in an "imperative" context (i.e., inside a method)

ghost function TreeAsSequence(tree:Tree) : seq<int>
{
  /*{*/
  if tree.Nil? then []
  else
    TreeAsSequence(tree.left) + [tree.value] + TreeAsSequence(tree.right)
  /*}*/
}

// If this predicate is true about sorted sequences, then everything
// in seq1 is <= everything in seq2.
ghost predicate SequencesOrderedAtInterface(seq1:seq<int>, seq2:seq<int>)
{
  if |seq1|==0 || |seq2|==0
  then true
  else Last(seq1) <= seq2[0]
}

// Write a recursive definition for what it means for a Tree to be sorted
ghost predicate IsSortedTree(tree:Tree) {
  /*{*/
  if tree.Nil? then true
  else
    && IsSortedTree(tree.left)
    && IsSortedTree(tree.right)
    && SequencesOrderedAtInterface(TreeAsSequence(tree.left), [tree.value])
    && SequencesOrderedAtInterface([tree.value], TreeAsSequence(tree.right))

  /*}*/
}

// You may find it useful to relate your recursive definition of IsSortedTree to
// a sequential representation of the tree structure

datatype TreeSortedness = Unsorted | Empty | Bounded(low: int, high: int)

// Write a recursive implementation that checks if a tree
// is sorted by checking the children, then using TreeAsSequence
// on the children to confirm that both children stay on their
// respective sides of the pivot.
method CheckIfSortedTree(tree:Tree) returns (out: TreeSortedness)
  ensures IsSortedTree(tree) <==> !out.Unsorted?
  /*{*/
  ensures tree.Nil? <==> out.Empty?
  ensures out.Bounded? ==>
            && out.low == TreeAsSequence(tree)[0]
            && out.high == Last(TreeAsSequence(tree))
  /*}*/
{
  /*{*/
  match tree {
    case Nil => {
      return Empty;
    }
    case Node(value, left, right) => {
      var left_sortedness := CheckIfSortedTree(left);
      var left_bound;
      match left_sortedness {
        case Unsorted => { return Unsorted; }
        case Empty => { left_bound := value; }
        case Bounded(left_low, left_high) => {
          if !(left_high <= value) {
            return Unsorted;
          } else {
            left_bound := left_low;
          }
        }
      }
      var rightSortedness := CheckIfSortedTree(right);
      var right_bound;
      match rightSortedness {
        case Unsorted => { return Unsorted; }
        case Empty => { right_bound := value; }
        case Bounded(right_low, right_high) => {
          if !(value <= right_low) {
            return Unsorted;
          } else {
            right_bound := right_high;
          }
        }
      }
      return Bounded(left_bound, right_bound);
    }
  }

  /*}*/
}






