include "../predicates.dfy"

method copy(src:array<int>, i:int, dest:array<int>, j:int, len:int)
  requires 0 <= i < src.Length && 0 <= j < dest.Length && 0 <= len
  // Source array must contain enough elements to be copied and
  // and target array must have enough space for copied elements
  requires src.Length >= i+len && dest.Length >= j+len
  // Source and target must be different arrays
  requires src != dest
  modifies dest
  // Source is unchanged
  ensures src[..] == old(src[..])
  // All elements before anf after copied region are same
  ensures dest[..j] == old(dest[..j]) && (dest[j+len..]) == old(dest[j+len..])
  // Copied region
  ensures dest[j..j+len] == src[i..i+len]
{
    var k := 0;
    while (k < len)
      invariant 0 <= k <= len
      invariant dest[..j] == old(dest[..j]) && (dest[j+len..]) == old(dest[j+len..])
      invariant dest[j..j+k] == src[i..i+k]
    {
        dest[j+k] := src[i+k];
        k := k+1;
    }
}