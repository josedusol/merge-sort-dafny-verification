
include "../predicates.dfy"

method {:isolate_assertions} {:timeLimitMultiplier 10} merge(a:array<int>, b:array<int>, c:array<int>)
  requires sorted(a[..]) && sorted(b[..])
  requires c.Length == a.Length + b.Length 
  modifies c
  ensures sorted(c[..])
  ensures multiset(c[..c.Length]) == multiset(a[..a.Length] + b[..b.Length])
  ensures a[..] == old(a[..]) &&  b[..] == old(b[..])
{
  var i, j, k := 0, 0, 0;
  while i < a.Length && j < b.Length
    invariant 0 <= i <= a.Length && 0 <= j <= b.Length && k == i + j 
    invariant sorted(c[..k])
    invariant forall m, n :: 0 <= m < k && i <= n < a.Length ==> c[m] <= a[n]
    invariant forall m, n :: 0 <= m < k && j <= n < b.Length ==> c[m] <= b[n]
    invariant a[..] == old(a[..]) && b[..] == old(b[..])
    invariant multiset(c[..k]) == multiset(a[..i] + b[..j])
  {
    if a[i] <= b[j] {
      c[k] := a[i];
      i := i + 1;
    } else {
      c[k] := b[j];
      j := j + 1;
    }
    k := k + 1;
  }

  if (i < a.Length) { 
    while i < a.Length
      invariant 0 <= i <= a.Length  &&  0 <= k <= c.Length &&  k == i + j
      invariant sorted(c[..k])
      invariant forall m, n :: 0 <= m < k && i <= n < a.Length ==> c[m] <= a[n] 
      invariant a[..] == old(a[..]) && b[..] == old(b[..]) 
      invariant multiset(c[..k]) == multiset(a[..i]) + multiset(b[..j])  
    {
      c[k] := a[i];
      i, k := i+1, k+1;
    }
  }
  if (j < b.Length) { 
    while j < b.Length
      invariant 0 <= j <= b.Length  &&  0 <= k <= c.Length  &&  k == i + j
      invariant sorted(c[..k])
      invariant forall m, n :: 0 <= m < k && j <= n < b.Length ==> c[m] <= b[n]
      invariant a[..] == old(a[..]) && b[..] == old(b[..]) 
      invariant multiset(c[..k]) == multiset(a[..i]) + multiset(b[..j])
    {
      c[k] := b[j];
      j, k := j+1, k+1;
    }
  }
  assert i == a.Length && j == b.Length && k == i + j == c.Length;
}