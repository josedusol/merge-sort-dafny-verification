include "../predicates.dfy"
include "../lemmas.dfy"

function fp (x : int, b : array<int>, l : int, r : int) : (m : int)
  reads b
  requires 0 <= l <= r <= b.Length
  requires sorted (b[l..r])
  ensures l <= m <= r
  ensures forall i :: l <= i < m ==> b[i] <= x
  ensures forall i :: m <= i < r ==> x <= b[i]
  decreases r-l
{
  if l == r 
    then l
    else
      var p := (l+r)/2 ;
        assert l <= p < r ;
      if x == b[p] 
        then p
        else 
            assert sorted (b[l..p]) && sorted (b[p..r]) by { 
              sub_sorted (b[l..r], 0, r-l, p-l) ;
              assert (b[l..r])[0..p-l] == b[l..p] ;
            }
        if x < b[p] 
          then fp (x, b, l, p)
          else fp (x, b, p+1, r)
}