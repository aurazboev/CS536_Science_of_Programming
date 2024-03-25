method notin(a: seq<int>) returns (r: int)
  ensures (forall i: int :: i >= 0 && i < |a| ==> a[i] != r)
{
  r := 0;
  var i := 0;
  while (i < |a|)
    invariant (0 <= i <= |a| && forall k: int :: k >= 0 && k < i ==> a[k] != r)
    
  {
    if (a[i] == r) {
      r := r + 1;
      i:=0;
    } else {
      i := i + 1;
    }
  }
}
