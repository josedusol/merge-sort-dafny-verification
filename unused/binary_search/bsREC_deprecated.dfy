include "../predicates.dfy"
include "../lemmas.dfy"

method bs (x : int, s : seq<int>, l : int, r : int) returns (m : int)
  requires 0 <= l <= r <= |s|
  requires sorted (s[l..r])
  ensures 0 <= l <= m <= r <= |s|
  ensures leqs_elem (s[l..m], x)
  ensures elem_leqs (x, s[m..r])
  decreases r-l
{
  if l == r {
    m := l;
  }else{
    m := (l+r)/2;
    if x==s[m]{
      increasing_sub(s,l,r,l,m);
      maximum(s,l,m);
      assert leqs_elem (s[l..m], x) ;
    }else if x<s[m] {
      increasing_sub(s,l,r,l,m);
      m := bs(x,s,l,m);
      increasing_sub(s,l,r,l,m);
      minimum(s,m,r);
      assert elem_leqs (x, s[m..r]) ;
    }else{
      m := bs(x,s,m+1,r);
      increasing_sub(s,l,r,l,m);
    }
  }
}