method copy (a : array<int>, i : nat, d : nat, a': array<int>, i' : nat, d' : nat)
  requires d-i == d'-i'
  requires 0 <= i <= d <= a.Length
  requires 0 <= i' <= d' <= a'.Length
  requires a != a'
  modifies a
  ensures a'[..] == old(a'[..])
  ensures a[i..d] == a'[i'..d']
  ensures a[0..i] == old(a[0..i])
  ensures a[d..a.Length] == old(a[d..a.Length])
{
  var s := a'[i'..d'];
  copy'(a,i,d,s);
}

method copy' (a : array<int>, i : nat, d : nat, s: seq<int>)
  requires 0 <= i <= d <= a.Length
  requires 0 <= |s|
  requires d-i == |s|
  modifies a
  ensures a[i..d] == s[0..|s|]
  ensures a[0..i] == old(a[0..i])
  ensures a[d..a.Length] == old(a[d..a.Length])
  decreases |s|
  decreases d-i
{
  if |s| == 0
    { }
  else if |s| == 1
    { a[i] := s[0]; }
  else 
    {
      var m := (i+d)/2;
      var m' := |s|/2;
      var s' := s[0..m'];
      var s'' := s[m'..|s|];
      assert s[0..|s|] == s'+s'';
      copy'(a,i,m,s');
      copy'(a,m,d,s'');
    }
}