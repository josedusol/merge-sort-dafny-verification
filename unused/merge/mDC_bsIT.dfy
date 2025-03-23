include "../predicates.dfy"
include "../lemmas.dfy"
include "../binary_search/bsIT.dfy"

method {:isolate_assertions} merge(a : array<int>, l : int, r : int, b : array<int>, l' : int, r' : int) returns (c : array<int>)
  requires 0 <= l <= r <= a.Length
  requires 0 <= l' <= r' <= b.Length
  requires sorted (a[l..r])
  requires sorted (b[l'..r'])
  ensures c.Length == r-l + r'-l'
  ensures sorted (c[0 .. c.Length])
  ensures perm (a[l..r]+b[l'.. r'], c[0..c.Length])
  ensures a[0..l] == old(a[0..l]) && a[r..a.Length] == old(a[r..a.Length])
  ensures b[0..l'] == old(b[0..l']) && b[r'..b.Length] == old(b[r'..b.Length])
  ensures c != a
  ensures c != b
  decreases r-l
{
  if r-l == 0 {
    c := new int[r'-l'] ((i) requires 0  <= i < r'-l' reads b => b[i+l']) ;
    assert c[0..c.Length] == b[l'..r'] ;
  } else {
    if r'-l' == 0  {
      c := new int[r-l] ((i) requires 0  <= i < r-l reads a => a[i+l]) ;
      assert c[0..c.Length] == a[l..r] ;
    } else {
      var m := (l+r)/2 ;

      increasing_sub_leqs_elem (a[..], l, r, m) ;
      assert leqs_elem (a[l..m], a[m]) ;
      assert elem_leqs (a[m], a[m..r]) ;

      var m' := bs (b, l', r', a[m]) ;
      assert b[..] == old(b[..]);

      assert leqs_elem (b[l'..m'], a[m]) ;
      assert elem_leqs (a[m], b[m'..r']) ;

      var d : array<int> := new int[m-l + m'-l'] ;

      increasing_sub (a[..], l, r, l, m) ;
      increasing_sub (b[..], l', r', l', m') ;

      d := merge (a, l, m, b, l', m') ;

      assert perm (a[l..m] + b[l'..m'], d[0..d.Length]) ;
      leqs_elem_sum (a[l..m], b[l'..m'], a[m]) ;
      leqs_elem_perm (a[l..m] + b[l'..m'], d[0..d.Length], a[m]) ;
      assert leqs_elem (d[..], a[m]) ;

      var d' : array<int> := new int[r-(m+1) + r'-m'] ;

      increasing_sub (a[..], l, r, m+1, r) ;
      increasing_sub (b[..], l', r', m', r') ;

      d' := merge (a, m+1, r, b, m', r') ;

      assert perm (a[m+1..r] + b[m'..r'], d'[0..d'.Length]) ;
      elem_leqs_sum (a[m+1..r], b[m'..r'], a[m]) ;
      elem_leqs_perm (a[m+1..r] + b[m'..r'], d'[0..d'.Length], a[m]) ;
      assert elem_leqs (a[m], d'[..]) ;

      c := new int[r-l + r'-l']
        ((i) requires 0  <= i < r-l + r'-l' reads d reads d' reads a =>  
          if i < m-l + m'-l' then 
            d[i]
          else if i > m-l + m'-l' then 
            d'[i - (m-l + m'-l') - 1]
          else 
            a[m]
        ) ;

      assert leqs_elem (c[0..m-l + m'-l'], a[m]) ;
      assert elem_leqs (a[m], c[m-l + m'-l'+1 .. c.Length]) ;
      assert c[m-l + m'-l'+1 .. c.Length] == d'[0..d'.Length] ;
      assert sorted (c[0..m-l + m'-l']) ;
      assert sorted (c[m-l + m'-l'+1 .. c.Length]) ;
      assert c[0..c.Length] == d[0..d.Length] + [a[m]] + d'[0..d'.Length] ;
      assert a[l..r] == a[l..m]+a[m..r] == a[l..m] + [a[m]] + a[m+1..r];
      assert b[l'.. r'] == b[l'..m']+b[m'..r'] ;
      assert perm (a[l..r]+b[l'.. r'], d[0..d.Length] + [a[m]] + d'[0..d'.Length]) ;
    }
  }
}