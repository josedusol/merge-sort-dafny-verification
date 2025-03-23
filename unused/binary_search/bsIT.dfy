
include "../predicates.dfy"
include "../lemmas.dfy"

method {:timeLimitMultiplier 2} bs(A:array<int>, l:int, r:int, x:int) returns (i:int)
  requires 0 <= l <= r <= A.Length
  requires sorted(A[l..r]) 
  ensures 0 <= l <= i <= r <= A.Length
  ensures leqs_elem(A[l..i], x)
  ensures elem_leqs(x, A[i..r])
  ensures A[..] == old(A[..])
{
  i := l; var j := r;
  while i != j
    invariant 0 <= l <= i <= r  &&  i <= j <= r  &&  sorted(A[l..i])  &&  sorted(A[j..r]) 
    invariant leqs_elem(A[l..i], x) && elem_leqs(x, A[j..r])
    invariant A[..] == old(A[..])
    decreases j-i
  {
    var m := (i+j)/2;
    
    assert i >= 0 && j > 0 && i < j; 
    assert i+j < 2*j;
    assert (i+j)/2 < j;

    if A[m] <= x {
      increasing_sub (A[..], l, r, l, m+1);
      assert sorted(A[l..m+1]); 
      assert A[l..m+1] == A[l..i] + A[i..m] + [A[m]];
      assert sorted(A[i..m+1]); 
      assert leqs_elem(A[i..m+1], x);
      assert leqs_elem(A[l..m+1], x);
      i := m+1;
      assert sorted(A[l..i]); 
    } else if x <= A[m] {  assert x < A[m];
      j := m;   
      assert sorted(A[j..r]); 
    } 
  }
}