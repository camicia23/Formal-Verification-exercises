//#title IsPrimeSpec I
//#desc Basic specification.
// Implement a predicate that tells whether a natural number is prime.

/*{*/
/*}*/
ghost predicate IsPrimeSpec(candidate:nat)
{
  /*{*/
  !(exists n,m:nat | 1 < n <= m <= candidate :: n*m == candidate) && candidate > 1
  /*}*/
}

// illustrate IsPrimeSpec on a few examples (note that the verifier is able to
// check these only with some help to find divisors for non-prime numbers)
lemma ConstantObligations()
  ensures !IsPrimeSpec(0)
  ensures !IsPrimeSpec(1)
  ensures IsPrimeSpec(2)
  ensures IsPrimeSpec(3)
  ensures !IsPrimeSpec(4)
  ensures !IsPrimeSpec(6)
  ensures IsPrimeSpec(7)
  ensures !IsPrimeSpec(9)
{
  /*{*/
  assert 2*2==4;
  assert 2*3==6;
  assert 3*3==9;
  /*}*/
}

lemma CompositeIsntPrime(p: nat)
  requires 1 < p
  ensures !IsPrimeSpec(p*66)
{
  /*{*/
  assert p*66 == p*66 && 66*p == p*66;  // LOL
  /*}*/
}


