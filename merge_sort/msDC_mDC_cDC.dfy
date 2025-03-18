include "../predicates.dfy"
include "../merge/mDC.dfy"
include "../copy/cDC.dfy"

method mergeSort(a : array<int>)
  requires 0 <= a.Length
  modifies a
  ensures perm(a[0..a.Length],old(a[0..a.Length]))
  ensures sorted(a[0..a.Length])
{
  if a.Length != 0
  { mergeSort'(a,0,a.Length-1); }
}

method {:isolate_assertions} {:timeLimitMultiplier 10} mergeSort'(a : array<int>, l : int, r : int)
  modifies a
  requires 0 <= l <= r < a.Length
  ensures perm(a[l..r+1],old(a[l..r+1]))
  ensures unch(a[..], old(a[..]),l,r)
  ensures sorted(a[l..r+1])
  decreases r-l
{
  if r-l > 0
  {
    var m := (l+r)/2;
    mergeSort'(a,l,m);
    assert forall i : int :: m+1 <= i < a.Length ==> a[i] == old(a[i]);
    assert a[m+1..r+1] == old(a[m+1..r+1]);
    mergeSort'(a,m+1,r);
    assert a[l..m+1] + a[m+1..r+1] == a[l..r+1];
    assert old(a[l..m+1]) + old(a[m+1..r+1]) == old(a[l..r+1]);
    var c := merge(a,l,m+1,a,m+1,r+1);
    assert c != a;
    copy(a,l,r+1,c,0,c.Length);
  }
}