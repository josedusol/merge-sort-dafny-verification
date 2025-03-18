include "../copy/cIT.dfy"
include "../predicates.dfy"

method {:isolate_assertions} {:timeLimitMultiplier 10} merge (a: array<int>, l: int, m: int, r: int)
  requires 0 <= l <= m < r < a.Length
  modifies a
  requires sorted(a[l..m+1]) && sorted(a[m+1..r+1])
  ensures sorted(a[l..r+1])
  ensures perm(a[l..r+1], old(a[l..r+1]))
  ensures unch(a[..],old(a[..]),l,r)
{
  var n1 := m - l + 1;
  var n2 := r - m;

  var left  := new int[n1];
  var right := new int[n2];

  left := copy(a,l,left,0,n1);
  right := copy(a,m+1,right,0,n2);

  assert (left[0..n1]==old(a[l..m+1]) && right[0..n2]==old(a[m+1..r+1]));

  var i, j, k := 0, 0, l;
  while i < n1 && j < n2
    invariant 0 <= i <= n1 && 0 <= j <= n2 && l <= k <= l + i + j && k == l + i + j
    invariant sorted(a[l..k]) && sorted(left[0..n1]) && sorted(right[0..n2])
    invariant forall i2, j2 :: l <= i2 < k && i <= j2 < n1 ==> a[i2] <= left[j2]
    invariant forall i2, j2 :: l <= i2 < k && j <= j2 < n2 ==> a[i2] <= right[j2]
    invariant multiset(a[l..k]) == multiset(left[0..i] + right[0..j])
    invariant perm(a[l..k],left[0..i] + right[0..j])
    invariant left[0..n1]==old(a[l..m+1]) && right[0..n2]==old(a[m+1..r+1])
    invariant unch(a[..],old(a[..]),l,r)
  {
    if left[i] <= right[j] {
      a[k] := left[i];
      i := i + 1;
    } else {
      a[k] := right[j];
      j := j + 1;
    }
    k := k + 1;
  }

  assert forall j2 :: i+1 <= j2 < n1 ==> left[i] <= left[j2];

  if (i < n1) {
    while i < n1
      invariant 0 <= i <= n1  && j == n2 && l <= k <= l + i + j && k == l + i + j
      invariant sorted(a[l..k]) && sorted(left[0..n1])
      invariant forall j2 :: i+1 <= j2 < n1 ==> left[i] <= left[j2]
      invariant forall i2, j2 :: l <= i2 < k && i <= j2 < n1 ==> a[i2] <= left[j2]
      invariant perm(a[l..k],left[0..i] + right[0..j])
      invariant left[0..n1]==old(a[l..m+1]) && right[0..n2]==old(a[m+1..r+1])
      invariant unch(a[..],old(a[..]),l,r)
    {
      a[k] := left[i];
      i, k := i+1, k+1;
    }
  }
  if (j < n2) {
    while j < n2
      invariant 0 <= j <= n2  && i == n1 && l <= k <= l + i + j && k == l + i + j
      invariant sorted(a[l..k]) && sorted(right[0..n2])
      invariant forall j2 :: j+1 <= j2 < n2 ==> right[j] <= right[j2]
      invariant forall i2, j2 :: l <= i2 < k && j <= j2 < n2 ==> a[i2] <= right[j2]
      invariant perm(a[l..k],left[0..i] + right[0..j])
      invariant left[0..n1]==old(a[l..m+1]) && right[0..n2]==old(a[m+1..r+1])
      invariant unch(a[..],old(a[..]),l,r)
    {
      a[k] := right[j];
      j, k := j+1, k+1;
    }
  }

  assert i == n1 && j == n2 && k == l + i + j;
  assert perm(a[l..r+1],left[0..n1] + right[0..n2]);
  assert old(a[l..r+1]) == old(a[l..m+1]) + old(a[m+1..r+1]);
  assert old(a[l..r+1]) == left[0..n1] + right[0..n2];
  assert unch(a[..],old(a[..]),l,r);
}