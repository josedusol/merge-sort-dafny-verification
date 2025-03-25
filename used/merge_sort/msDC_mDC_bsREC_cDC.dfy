include "../predicates.dfy"
include "../merge/mDC_bsREC.dfy"
include "../copy/cDC.dfy"

method merge_sort (a : array<int>)
  modifies a
  ensures sorted (a[0..a.Length]) && perm (a[0..a.Length], old(a[0..a.Length]))
{
  merge_sort' (a, 0, a.Length) ;
}

method merge_sort' (a : array<int>, l : int, r : int)
  modifies a
  requires 0 <= l <= r <= a.Length
  ensures sorted (a[l..r])
  ensures perm (a[l..r], old (a[l..r]))
  ensures a[0..l] == old (a[0..l])
  ensures a[r..a.Length] == old (a[r..a.Length])
  decreases r - l
{
  if r-l < 2 {}
  else {
    var m := (r+l)/2 ;
    merge_sort' (a, l, m) ;
    calc {
      a[m..a.Length] == old(a[m..a.Length]);
    ==> { sub_eq(a[..],old(a[..]),m,r,a.Length); }
      a[m..r] == old(a[m..r]);
    ==>
      perm (a[m..r],old(a[m..r]));
    ==> { assert a[l..r] == a[l..m] + a[m..r];
          assert old(a[l..r]) == old(a[l..m])+old(a[m..r]);
          perm_sum(a[l..m],old(a[l..m]),a[m..r],old(a[m..r]));
         }
      perm(a[l..r], old(a[l..r]));
    }
    label bfr:
    merge_sort' (a, m, r) ;
    calc {
      a[0..m] == old@bfr(a[0..m]);
    ==> { sub_eq(a[..],old@bfr(a[..]),0,l,m); }
      a[l..m] == old@bfr(a[l..m]);
    ==>
      perm (a[l..m],old@bfr(a[l..m]));
    ==> { assert a[l..r] == a[l..m] + a[m..r];
          assert old@bfr(a[l..r]) == old@bfr(a[l..m])+old@bfr(a[m..r]);
          perm_sum(a[l..m],old(a[l..m]),a[m..r],old@bfr(a[m..r]));
         }
      perm(a[l..r], old@bfr(a[l..r]));
    }
    merge' (a, l, m, r) ;
  }
}

method {:axiom} merge' (a : array<int>, l : int, m : int, r : int)
  modifies a
  requires 0 <= l < m < r <= a.Length
  requires sorted (a[l..m]) && sorted (a[m..r])
  ensures sorted (a[l..r])
  ensures perm (a[l..r], old(a[l..r]))
  ensures a[0..l] == old (a[0..l]) && a[r..a.Length] == old (a[r..a.Length])
{
    var c := merge(a,l,m,a,m,r);
    assert a[l..r]==a[l..m]+a[m..r];
    assert perm(a[l..r],c[..]);
    assert c[..] == c[0..c.Length];
    copy(a,l,r,c,0,c.Length);
    assert perm(old(a[l..r]),c[..]);
    assert perm(a[l..r],c[0..c.Length]);
}
