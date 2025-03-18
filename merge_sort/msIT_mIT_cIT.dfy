include "../predicates.dfy"
include "../lemmas.dfy"
include "../merge/mIT.dfy"
include "../copy/cIT.dfy"

method mergeSort (a : array<int>)
  modifies a
  requires a.Length >= 1
  ensures sorted (a[..])
  ensures perm (a[..], old(a[..]))
{
  var s : int ;
  s := 1 ;
  while s < a.Length
    invariant 1 <= s
    invariant forall l :: (0 <= l < a.Length && l%s == 0) ==> sorted (a[l .. min(l+s, a.Length)])
    invariant perm (a[..], old(a[..]))
    decreases a.Length - s
  {
    merges (a, s) ;
    s := 2*s ;
  }
  assert 0%s == 0 ;
}

method merges (a : array<int>, s : int)
  modifies a
  requires 1 <= a.Length
  requires 1 <= s
  requires forall l :: (0 <= l < a.Length && l%s == 0) ==> sorted (a[l .. min(l+s, a.Length)])
  ensures forall l :: (0 <= l < a.Length && l%(2*s) == 0) ==> sorted (a[l .. min(l+2*s, a.Length)])
  ensures perm (a[..], old(a[..]))
{
  var j : int ;
  j := 0 ;
  while j != a.Length
    invariant 1 <= s
    invariant 0 <= j <= a.Length
    invariant j != a.Length ==> j%(2*s) == 0
    invariant forall l :: (0 <= l < j && l%(2*s) == 0) ==> sorted (a[l .. min(l+2*s, a.Length)])
    invariant forall l :: (j <= l < a.Length && l%s == 0) ==> sorted (a[l .. min(l+s, a.Length)])
    invariant perm (a[..], old(a[..]))
    decreases a.Length - j
  {
    assert j%(2*s) == 0 ; assert j%s == 0 by {modn_i (j, s) ;}
    assert sorted (a[j .. min(j+s, a.Length)]) ;
    assert sorted (a[min(j+s, a.Length) .. min(j+2*s, a.Length)])
    by {
      assert forall l :: (j <= l < a.Length && l%s == 0) ==> sorted (a[l .. min(l+s, a.Length)]) ;
      assert (j+s < a.Length && min(j+s, a.Length) == j+s) || (j+s >= a.Length && min(j+s, a.Length) == a.Length) ;
      assert 0 <= j+s < a.Length ==> (j+s)%s == 0
      by {
        modn (j, s) ;
      }
      assert a.Length <= j+s ==> a.Length <= j+2*s ;
    }
    label mergePair :
    mergePair (a, j, s) ;
    forall l : int | 0 <= l < min(j+2*s, a.Length) && l%(2*s) == 0
      ensures sorted (a[l .. min(l+2*s, a.Length)])
    {
      if l < j {
        assert a[0..j] == old@mergePair(a[0..j]) ;
        assert l < j ;
        assert 0 <= l < l+2*s <= j < a.Length by {mod2n_ii (j, l, 2*s) ;}
        subseq_eq (a[0..j], old@mergePair(a[0..j]), l, min(l+2*s, a.Length)) ;
        assert a[l .. min(l+2*s, a.Length)] == (a[0..j])[l .. min(l+2*s, a.Length)] by {sub_subseq (a[..], 0, j, l, min(l+2*s, a.Length)) ;}
        assert (a[0..j])[l .. min(l+2*s, a.Length)] == old@mergePair((a[0..j])[l .. min(l+2*s, a.Length)]) ;
        assert old@mergePair((a[0..j])[l .. min(l+2*s, a.Length)]) == old@mergePair(a[l .. min(l+2*s, a.Length)]) by {sub_subseq (old@mergePair(a[..]), 0, j, l, min(l+2*s, a.Length)) ;}
        assert sorted (old@mergePair(a[l .. min(l+2*s, a.Length)])) ;
        assert sorted (a[l .. min(l+2*s, a.Length)]) ;
      }
      else {
        mod2n_iii (j, l, 2*s) ; //assume l == j ;
        assert sorted (a[j .. min(j+2*s, a.Length)]) ;
      }
    }
    calc {
      j + 2*s < a.Length ;
    ==>
      j < a.Length ;
    ==> {
          assert j < a.Length ==> j != a.Length ==> j%(2*s) == 0 ;}
      j%(2*s) == 0 ;
    ==> {
          mod2n (j, 2*s) ;}
      (j + 2*s)%(2*s) == 0 ;
    }
    j := min (j + 2*s, a.Length) ;
    forall l : int | j <= l < a.Length && l%s == 0
      ensures sorted (a[l .. min(l+s, a.Length)])
    {
      assert a[j .. a.Length] == old@mergePair(a[j .. a.Length]) ;
      assert 0 <= l-j < min(l+s, a.Length)-j <= a.Length-j by {assert l < l+s && l < a.Length ;}
      subseq_eq (a[j .. a.Length], old@mergePair(a[j .. a.Length]), l-j, min(l+s, a.Length)-j) ;
      assert a[l .. min(l+s, a.Length)] == (a[j..a.Length])[l-j .. min(l+s, a.Length)-j] by {sub_subseq (a[..], j, a.Length, l, min(l+s, a.Length)) ;}
      assert (a[j..a.Length])[l-j .. min(l+s, a.Length)-j] == old@mergePair((a[j..a.Length])[l-j .. min(l+s, a.Length)-j]) ;
      assert old@mergePair((a[j..a.Length])[l-j .. min(l+s, a.Length)-j]) == old@mergePair(a[l..min(l+s, a.Length)]) by {sub_subseq (old@mergePair(a[..]), j, a.Length, l, min(l+s, a.Length)) ;}
      assert sorted (old@mergePair(a[l .. min(l+s, a.Length)])) ;
      assert sorted (a[l .. min(l+s, a.Length)]) ;
    }
  }
}

method {:isolate_assertions} {:timeLimitMultiplier 10} mergePair (a : array<int>, l : int, s : int)
  modifies a
  requires 0 <= l < a.Length
  requires s >= 1
  requires sorted (a[l .. min (l+s, a.Length)])
  requires sorted (a[min (l+s, a.Length) .. min (l+2*s, a.Length)])
  ensures sorted (a[l .. min (l+2*s, a.Length)])
  ensures perm (a[..], old(a[..]))
  ensures a[0..l] == old(a[0..l])
  ensures a[min (l+2*s, a.Length)..a.Length] == old(a[min (l+2*s, a.Length)..a.Length])
  {
    if (l+s >= a.Length){}
    else{
      var aa := new int[s];
      var s' := min(s,a.Length-(l+s));
      var aa' := new int[s'];
      var a' := new int[s+s'];

      copy(a,l,aa,0,s);
      assert old(a[l..l+s])==aa[0..s];

      copy(a,l+s,aa',0,s');
      assert old(a[l+s..l+s+s'])==aa'[0..s'];
      assert old(a[l..l+s+s'])==aa[0..s]+aa'[0..s'];

      merge(aa,aa',a');

      copy(a',0,a,l,s+s');
      assert a[..] == a[0..l]+a[l..l+s+s']+a[l+s+s'..a.Length];
      assert old(a[..]) == old(a[0..l]+a[l..l+s+s']+a[l+s+s'..a.Length]);
      assert perm(a[..],old(a[..]));
    }
  }

function min (x : int, y : int) : (m : int)
  ensures m <= x
  ensures m <= y
  ensures m == x || m == y
{
  if x < y then x else y
}