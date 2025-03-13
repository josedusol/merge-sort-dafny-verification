include "predicates.dfy"

lemma {:axiom} trivial_increasing (s : seq<int>)
  ensures |s| < 2 ==> sorted (s)

lemma {:axiom} increasing_sub (s : seq<int>, l: int, r : int, i : int, j : int)
  requires 0 <= l <= i <= j <= r <= |s|
  requires sorted (s[l..r])
  ensures  sorted (s[i..j])

lemma {:axiom} increasing_sub_leqs (s : seq<int>, l: int, r : int, m : int)
  requires 0 <= l <= m < r <= |s|
  requires sorted (s[l..m])
  requires sorted (s[m+1..r])
  requires leqs_elem (s[l..m], s[m])
  requires elem_leqs (s[m], s[m+1..r])     
  ensures sorted (s[l..r])

lemma {:axiom} increasing_sub_leqs_elem (s : seq<int>, l: int, r : int, m : int)
  requires 0 <= l <= m < r <= |s|
  requires sorted (s[l..r])
  ensures  leqs_elem (s[l..m], s[m]) && elem_leqs (s[m], s[m..r])

lemma {:axiom} leqs_elem_sum (s : seq<int>, s' : seq<int>, x : int)
  requires leqs_elem (s, x) && leqs_elem (s', x)
  ensures leqs_elem (s + s', x)

lemma {:axiom} elem_leqs_sum (s : seq<int>, s' : seq<int>, x : int)
  requires elem_leqs (x, s) && elem_leqs (x, s')
  ensures elem_leqs (x, s + s')

lemma {:axiom} elem_leqs_sub (s : seq<int>, l : int, r : int, m : int, x : int)
  requires 0 <= l <= m < r <= |s|
  requires sorted (s[l..r])
  ensures elem_leqs (x, s[l..m]) ==> elem_leqs (x, s[l..r])

lemma {:axiom} leqs_elem_sub (s : seq<int>, l : int, r : int, m : int, x : int)
  requires 0 <= l <= m <= r <= |s|
  requires sorted (s[l..r])
  ensures leqs_elem (s[m..r], x) ==> leqs_elem (s[l..r], x)

lemma perm_refl (s : seq<int>)
  ensures perm (s, s)
{}

lemma {:axiom} leqs_elem_perm (s : seq<int>, s' : seq<int>, x : int)
  requires leqs_elem (s, x) 
  requires perm (s, s')
  ensures leqs_elem (s', x)

lemma {:axiom} elem_leqs_perm (s : seq<int>, s' : seq<int>, x : int)
  requires elem_leqs (x, s) 
  requires perm (s, s')
  ensures elem_leqs (x, s')