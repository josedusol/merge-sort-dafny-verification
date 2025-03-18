include "../predicates.dfy"

function {:axiom} bs (x : int, s : seq<int>, l : int, r : int) : (m : int)
  requires 0 <= l < r <= |s|
  requires sorted (s[l..r])
  ensures l <= m <= r
  ensures leqs_elem (s[l..m], x)
  ensures elem_leqs (x, s[m..r])
  decreases r-l
{
  var p := (l+r)/2 ;
  if x == s[p] then
    //increasing_sub_leqs_elem (s, l, r, p) ;
    p
  else if x < s[p] then
    if l == p then
      p
    else
      var m := (/*increasing_sub (s, l, r, l, p) ;*/ bs (x, s, l, p)) ;
      //increasing_sub (s, l, r, m, r) ; 
      //elem_leqs_sub (s, m, r, p, x) ;
      m
  else if p+1 == r then
    //leqs_elem_sub (s, l, r, p, x) ;
    r
  else
    var m := (/*increasing_sub (s, l, r, p+1, r) ;*/ bs (x, s, p+1, r)) ;
    //increasing_sub (s, l, r, l, m) ;
    //leqs_elem_sub (s, l, m, p+1, x) ;
    m
}