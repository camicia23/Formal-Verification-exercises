//#title Fibo
//#desc Recursion challenge.

ghost function fibo(val:nat) : nat
{
  /*{*/
  // if val == 0 then 0 else if val == 20 then 6765 else 0 lol
  if val == 0 then 0 else if val == 1 then 1 else fibo(val-1) + fibo(val-2)
  /*}*/
}

lemma Check()
  ensures fibo(0) == 0
  ensures fibo(20) == 6765
{
}

