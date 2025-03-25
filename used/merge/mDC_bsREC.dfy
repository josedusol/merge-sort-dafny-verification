include "../predicates.dfy"
include "../lemmas.dfy"
include "../find_place/fpREC.dfy"

method mergeGen (a : array<int>, l : int, r : int, b : array<int>, l' : nat, r' : nat) returns (c : array<int>)
  requires 0 <= l <= r <= a.Length
  requires 0 <= l' <= r' <= b.Length
  requires sorted (a[l..r])
  requires sorted (b[l'..r'])
  ensures c.Length == r-l + r'-l'
  ensures sorted (c[..])
  ensures perm (a[l..r]+b[l'.. r'], c[..])
  ensures a[l..r] == old(a[l..r])
  ensures b[l'..r'] == old(b[l'..r'])
  ensures a != c
  decreases r-l
{
  if r-l == 0 {
    c := new int[r'-l'] ((i) requires 0  <= i < r'-l'
                         reads b
                         => b[i+l']) ;
    assert c[..] == b[l'..r'] ;
  }
  else{
    if r'-l' == 0 {
      c := new int[r-l] ((i) requires 0  <= i < r-l
                         reads a => a[i+l]) ;
      assert c[..] == a[l..r] ;
    }
    else{
      var m := (l+r)/2 ;
      calc {sorted (a[l..r]) ;
      ==> {
            assert l <= m < r ;
            sub_leqs (a[..], l, r, m) ;
          }
        leqs (a[l..m], a[m+1..r]) ;
      }
      assert forall i :: l <= i < m ==> a[i] <= a[m] ;
      assert forall i :: m < i < r ==> a[m] <= a[i] ;
      var m' := fp (a[m], b, l', r') ;
      calc {
        sorted (b[l'..r']) ;
      ==> {
            assert l' <= m' <= r' ;
            sub_leqs (b[..], l', r', m') ;
          }
        leqs (b[l'..m'], b[m'..r']) ;
      }
      assert forall i :: l' <= i < m' ==> b[i] <= a[m] ;
      assert forall i :: m' <= i < r' ==> a[m] <= b[i]  ;
      assert sorted (a[l..m]) &&  sorted (b[l'..m'])
      by {
        sub_sorted (a[..], l, r, m) ; sub_sorted (b[..], l', r', m') ;
      }
      label bfr :
      var d : array<int> := new int[m-l + m'-l'] ;
      d := mergeGen (a, l, m, b, l', m') ;
      var d' : array<int> := new int[r-(m+1) + r'-m'] ;
      d' := mergeGen (a, m+1, r, b, m', r') ;
      assert leqs (d[..], d'[..])
      by {
        assert a[l..r] == old@bfr(a[l..r]) && b[l'..r'] == old@bfr(b[l'..r']);
        assert leqs(a[l..m],a[m+1..r]);
        assert leqs(b[l'..m'],b[m'..r']);
        sum_leqs(a[l..m],a[m+1..r],b[l'..m'],b[m'..r']);
        assert leqs (a[l..m]+b[l'..m'], a[m+1..r]+b[m'..r']) ;
        assert perm (d[..], a[l..m]+b[l'..m']) && perm (d'[..], a[m+1..r]+b[m'..r']) ;
        perm_leqs (a[l..m]+b[l'..m'], a[m+1..r]+b[m'..r'], d[..], d'[..]) ;
      }
      calc { a[l..r] == old@bfr(a[l..r]) && b[l'..r'] == old@bfr(b[l'..r']) ;
      ==>
        forall i :: 0 <= i < d.Length ==> (a[l..m]+b[l'..m'])[i] <= a[m] ;
      ==>{
           assert perm (d[..], a[l..m]+b[l'..m']) ;
           perm_leqs (a[l..m]+b[l'..m'], [a[m]], d[..], [a[m]]) ;
         }
        forall i :: 0 <= i < d.Length ==> d[i] <= a[m] ;
      }
      calc {a[l..r] == old@bfr(a[l..r]) && b[l'..r'] == old@bfr(b[l'..r']) ;
      ==>
        forall i :: 0 <= i < d'.Length ==> a[m] <= (a[m+1..r]+b[m'..r'])[i] ;
      ==>{
           assert perm (d'[..], a[m+1..r]+b[m'..r']) ;
           perm_leqs ([a[m]], a[m+1..r]+b[m'..r'], [a[m]], d'[..]) ;
         }
        forall i :: 0 <= i < d'.Length ==> a[m] <= d'[i] ;
      }
      c := new int[r-l + r'-l']
      ((i) requires 0  <= i < r-l + r'-l'
       reads d reads d' reads a
       => if i < m-l + m'-l' then d[i]
       else if i > m-l + m'-l' then d'[i - (m-l + m'-l') - 1]
       else a[m]
      ) ;
      assert sorted (c[..]) ;
      assert perm (a[l..r]+b[l'.. r'], c[..])
      by {
        assert c[..] == d[..] + [a[m]] + d'[..] ;
        assert l <= m < r;
        assert a[l..r] == a[l..m] + [a[m]] + a[m+1..r] ;
        assert l' <= m' <= r';
        assert b[l'..r'] == b[l'..m'] + b[m'..r'] ;
      }
    }
  } assert perm (a[l..r]+b[l'.. r'], c[..]) ;
}