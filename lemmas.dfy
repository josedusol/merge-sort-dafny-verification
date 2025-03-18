include "predicates.dfy"

lemma trivial_increasing (s : seq<int>)
  ensures |s| < 2 ==> sorted (s)
{}

lemma increasing_sub (s : seq<int>, l: int, r : int, i : int, j : int)
  requires 0 <= l <= i <= j <= r <= |s|
  requires sorted (s[l..r])
  ensures  sorted (s[i..j])
{
  assert (l <= i < j < r ==> s[i] <= s[j]);
}

lemma increasing_sub_leqs (s : seq<int>, l: int, r : int, m : int)
  requires 0 <= l <= m < r <= |s|
  requires sorted (s[l..m])
  requires sorted (s[m+1..r])
  requires leqs_elem (s[l..m], s[m])
  requires elem_leqs (s[m], s[m+1..r])
  ensures sorted (s[l..r])
{
  assert (forall h : int, k : int :: l <= h < k < r ==> s[h] <= s[k]);
}

lemma increasing_sub_leqs_elem (s : seq<int>, l: int, r : int, m : int)
  requires 0 <= l <= m < r <= |s|
  requires sorted (s[l..r])
  ensures  leqs_elem (s[l..m], s[m]) && elem_leqs (s[m], s[m..r])
{
  assert (forall h : int, k : int :: l <= h < k < r ==> s[h] <= s[k]);
}


lemma leqs_elem_sum (s : seq<int>, s' : seq<int>, x : int)
  requires leqs_elem (s, x) && leqs_elem (s', x)
  ensures leqs_elem (s + s', x)
{}

lemma elem_leqs_sum (s : seq<int>, s' : seq<int>, x : int)
  requires elem_leqs (x, s) && elem_leqs (x, s')
  ensures elem_leqs (x, s + s')
{}

lemma elem_leqs_sub (s : seq<int>, l : int, r : int, m : int, x : int)
  requires 0 <= l < m <= r <= |s|
  requires sorted (s[l..r])
  ensures elem_leqs (x, s[l..m]) ==> elem_leqs (x, s[l..r])
  {
    calc{
      sorted(s[l..r]) && elem_leqs (x, s[l..m]);

      ==> {assert (forall h : int, k : int :: l <= h < k < m ==> s[h] <= s[k]);}

      sorted(s[l..m]) && elem_leqs (x, s[l..m]);
      
      ==> 

      x <= s[l];

      ==> 

      elem_leqs (x, s[l..r]);

    }    
  }

lemma leqs_elem_sub (s : seq<int>, l : int, r : int, m : int, x : int)
  requires 0 <= l <= m < r <= |s|
  requires sorted (s[l..r])
  ensures leqs_elem (s[m..r], x) ==> leqs_elem (s[l..r], x)
  {
    calc{
      sorted(s[l..r]) && leqs_elem (s[m..r],x);

      ==> {assert (forall h : int, k : int :: l <= h < k < m ==> s[h] <= s[k]);}

      sorted(s[l..m]) && leqs_elem (s[m..r], x);
      
      ==> 

      s[r-1] <= x;

      ==> 

      leqs_elem (s[l..r], x);

    }    
  }

lemma perm_refl (s : seq<int>)
  ensures perm (s, s)
{}

lemma leqs_elem_perm (s : seq<int>, s' : seq<int>, x : int)
  requires leqs_elem (s, x)
  requires perm (s, s')
  ensures leqs_elem (s', x)
{
  if !leqs_elem (s', x)
  {
    assert exists i :: 0 <= i < |s'| && s'[i] > x;
    assert false by {
      forall i : int | 0 <= i < |s'| && s'[i] > x
        ensures false
      {
        var a := s'[i];
        assert a in multiset(s');
        assert a in multiset(s) by {
          assert perm(s,s');
        }
      }
    }
  }
}

lemma elem_leqs_perm (s : seq<int>, s' : seq<int>, x : int)
  requires elem_leqs (x, s)
  requires perm (s, s')
  ensures elem_leqs (x, s')
{
  if !elem_leqs (x, s')
  {
    assert exists i :: 0 <= i < |s'| && s'[i] < x;
    assert false by {
      forall i : int | 0 <= i < |s'| && s'[i] < x
        ensures false
      {
        var a := s'[i];
        assert a in multiset(s');
        assert a in multiset(s) by {
          assert perm(s,s');
        }
      }
    }
  }
}

lemma subseq_eq (a : seq<int>, b : seq<int>, l : int, r : int)
  requires a == b
  requires 0 <= l < r <= |a|
  ensures a[l..r] == b[l..r]
{}

lemma {:axiom} sub_subseq (a : seq<int>, l : int, r : int, l' : int, r' : int)
  requires 0 <= l <= l' < r' <= r <= |a|
  ensures a[l'..r'] == (a[l..r])[l'-l..r'-l]


lemma {:axiom} modn_i (x : int, n : int)
  requires x >= 0 && n > 0
  requires x%(2*n) == 0
  ensures x%n == 0

lemma {:axiom} mod2n (x : int, n : int)
  requires x >= 0 && n > 0
  requires x%n == 0
  ensures (x+n)%n == 0

lemma {:axiom} mod2n_i (x : int, n : int, z : int)
  requires x >= 0 && n > 0
  requires x%(2*n) == 0
  requires 0 <= z < x+2*n
  ensures z <= x

lemma {:axiom} mod2n_ii (x : int, z : int, n : int)
  requires x >= 0 && n > 0
  requires x%n == 0
  requires z%n == 0
  requires 0 <= z < x
  ensures z+n <= x

lemma {:axiom} mod2n_iii (x : int, z : int, n : int)
  requires x >= 0 && n > 0
  requires x%n == 0
  requires z%n == 0
  requires x <= z < x+n
  ensures z == x

lemma {:axiom} modn (x : int, n : int)
  requires x >= 0 && n > 0
  requires x%n == 0
  ensures (x+n)%n == 0