include "../predicates.dfy"
include "../merge/mDC_bsREC_tato.dfy"
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
ensures a[0..l] == old (a[0..l]) && a[r..a.Length] == old (a[r..a.Length])
decreases r - l // required
{
    if r-l < 2 {}
    else {
        var m := (r+l)/2 ;
        merge_sort' (a, l, m) ;    
            assert forall i : int :: m <= i < a.Length ==> a[i] == old(a[i]);
            assert a[m..r] == old(a[m..r]);
        merge_sort' (a, m, r) ;
            assert a[l..m] + a[m..r] == a[l..r];
            assert old(a[l..m]) + old(a[m..r]) == old(a[l..r]);
        merge' (a, l, m, r) ;
            assert perm (a[l..r], old (a[l..r]));
            assert a[0..l] == old (a[0..l]) && a[r..a.Length] == old (a[r..a.Length]);
    }
}

method merge' (a : array<int>, l : int, m : int, r : int)
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
    assert a != c;
    label before_copy:
    copy(a,l,r,c,0,c.Length);
    assert perm(old(a[l..r]),c[..]);
    assert perm(a[l..r],c[0..c.Length]);
}
