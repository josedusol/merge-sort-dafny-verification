
method copy(src:array<int>, i:int, dest:array<int>, j:int, len:int) returns (r:array<int>)
  requires 0 <= i < src.Length && 0 <= j < dest.Length && 0 <= len
  // Source array must contain enough elements to be copied and
  // and target array must have enough space for copied elements
  requires src.Length >= i+len && dest.Length >= j+len
  // Source is unchanged
  ensures src[..] == old(src[..])
  // Result is same size as dest
  ensures r.Length == dest.Length
  // All elements before anf after copied region are same
  ensures r[..j] == dest[..j] && r[j+len..] == dest[j+len..]
  // Copied region
  ensures r[j..j+len] == src[i..i+len]
{
    if len == 0 { return dest; }
    
    r := new int[dest.Length];
    var k := 0;
    while (k < r.Length)
      invariant 0 <= k <= r.Length
      invariant r[..k] == dest[..k]
    {
        r[k] := dest[k];
        k := k+1;
    }
    assert r[..] == dest[..];

    k := 0;
    while (k < len)
      invariant 0 <= k <= len
      invariant r[..j] == dest[..j] && r[(j+len)..] == dest[(j+len)..]
      invariant r[j..j+k] == src[i..i+k]
    {
        r[j+k] := src[i+k];
        k := k+1;
    }
}