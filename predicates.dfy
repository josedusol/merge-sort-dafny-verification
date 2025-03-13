predicate sorted(s:seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate perm(a : seq<int>, a' : seq<int>)
{
  multiset(a) == multiset(a') && |a| == |a'|
}

predicate unch(a : seq<int>, a' : seq<int>, l : int, r : int)
  requires 0 <= l <= r < |a|
  requires |a| == |a'|
{
  (a[0..l] == a'[0..l] && a[r+1..|a|] == a'[r+1..|a|])
}

predicate leqs (s : seq<int>, s' : seq<int>)
{
  forall i, j :: 0 <= i < |s| && 0 <= j < |s'| ==> s[i] <= s'[j]
}

predicate leqs_elem (s : seq<int>, x : int)
{
  forall i :: 0 <= i < |s| ==> s[i] <= x
}

predicate elem_leqs (x : int, s : seq<int>)
{
  forall i :: 0 <= i < |s| ==> x <= s[i]
}