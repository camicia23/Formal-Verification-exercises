//#title Binary Search
//#desc Method implementation; writing a Hoare spec.

ghost predicate IsSorted(seqint:seq<int>) {
  forall i:nat,j:nat | i<j<|seqint| :: seqint[i] <= seqint[j]
}

// Write down the BinarySearch algorithm, which should return
// the index of the first element of the haystack that is >= to the needle.
// If the needle is present, this should be the index of the needle.
// If needle is bigger than every element, return the length of the
// sequence: It's not a valid index in the sequence, but it's bigger
// than the indices of all the elements that have smaller values.

method BinarySearch(haystack:seq<int>, needle:int) returns (index:nat)
  requires IsSorted(haystack)
  /*{*/
  ensures index <= |haystack|
  ensures forall i:nat | i < index :: haystack[i] < needle
  ensures index == |haystack| || haystack[index] >= needle
  /*}*/
{
  /*{*/

  // RECURSIVE
  if(|haystack| == 0){
    index := 0;
    return;
  } else if(|haystack| == 1){
    if needle > haystack[0] {
      index := 1;
    } else {
      index := 0;
    }
    return;
  }

  var size:nat := |haystack|;

  var m:nat := size/2;
  var ans:nat := BinarySearch(haystack[..m], needle);
  if ans == m {
    var add_pos:nat := BinarySearch(haystack[m..], needle);
    index := m + add_pos;
  } else {
    index := ans;
  }

  /*}*/
}


