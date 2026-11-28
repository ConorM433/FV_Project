
/*** Even ***/

 ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m;
	}
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
lemma EvenTimes(n1: int, n2: int)
  ensures isEven(n1) || isEven(n2) ==> isEven(n1 * n2)
{
  if isEven(n1) {
	var m1 := n1 / 2;
	assert n1 * n2 == 2 * (m1 * n2);
  } else if isEven(n2) {
	var m2 := n2 / 2;
	assert n1 * n2 == 2 * (n1 * m2);
  }
}

/*** Odd ***/

ghost predicate isOdd(n: int) {
  exists m: int :: n == 2 * m + 1
}
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}
lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{ // TODO
	if n % 2 != 0 {
	  var m := n / 2;
	  assert n == 2 * m + 1;
	}
}
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}
lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{ // TODO
	OddModulo(n);
	ModuloOdd(n);
}
lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{ // TODO
  if isOdd(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1 + m2) + 1;
  }
}

/*** Even & Odd ***/

lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{ 
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{ // TODO
  if n % 2 == 0 {
	ModuloEven(n);
  } else {
	ModuloOdd(n);
  }
}

lemma EvenTimesOdd(n1: int, n2: int)
  ensures isEven(n1) && isOdd(n2) ==> isEven(n1 * n2)
{ // TODO
  if isEven(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1);
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{ // TODO
	if isEven(n) {
		var m := invertParity(n);
		ModuloOdd(m);
	} else {
		var m := invertParity(n);
		ModuloEven(m);
	}
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
  forall i, j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == s[j] ==> i == j // TODO
}

// hint don't use return statements. Set b instead.
method checkSet(s: seq<int>) returns (b: bool)
  ensures b <==> isSet(s) //TODO
{ // TODO: fill in your code here and prove method correct
}

/* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
 isSet(s) && forall x :: x in s ==> isEven(x) // TODO
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  ensures b <==> isEvenSet(s)
{ // TODO: fill in your code here and prove method correct
}

/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  isSet(s) && forall x :: x in s ==> isOdd(x) // TODO
}

method checkOddSet(s: seq<int>) returns (b: bool)
  ensures b <==> isOddSet(s)
{ // TODO: fill in your code here and prove method correct
}

/*** Set Operations ***/

/* Adds n to a set s, making sure it remains a set */
// Hint: use recursion
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
  requires isSet(s)
  ensures isSet(b)
  ensures forall x :: (0 <= x < |b|) ==> (b[x] in s || b[x] == n)
  ensures forall x :: (0 <= x < |s|) ==>  s[x] in b
  ensures n in s ==> b == s
  ensures !(n in s) ==> b == s + [n]
  ensures isEvenSet(s) && isEven(n) ==> isEvenSet(b)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(b)
{ // TODO: fill in your code here and prove method correct
  if n in s {
    b := s;
  } else {
    b := s + [n];
  }
}

/* unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 || t[x] in s2)
  ensures forall x :: (0 <= x < |s1| ==> s1[x] in t)
  ensures forall x :: (0 <= x < |s2| ==> s2[x] in t)
  ensures isEvenSet(s1) && isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{ // TODO: fill in your code here and prove method correct
  t := s1;

  for i := 0 to |s2|
    invariant 0 <= i <= |s2|
    invariant isSet(t)
    invariant forall x: int ::
      x in t <==> (x in s1 || x in s2[..i])
  {
    t := addToSet(t, s2[i]);
  }
}

/* intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && t[x] in s2)
  ensures forall x, y :: (0 <= x < |s1| && 0 <= y < |s2| && s1[x] == s2[y]) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
{
  t := [];

  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant |t| <= i
    invariant isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
    invariant forall x: int ::
      x in t <==> (x in s1[..i] && x in s2)
  {
    if s1[i] in s2 {
      if isEvenSet(s1) && isOddSet(s2) {
        assert s1[i] in s1;
        NotEvenANDOdd(s1[i]);
        assert false;
      }
      t := t + [s1[i]];
    }
  }

  forall k | 0 <= k < |t|
    ensures t[k] in s1 && t[k] in s2
  {
    assert t[k] in t;
  }
}

/* difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && !(t[x] in s2))
  ensures forall x :: (0 <= x < |s1| && !(s1[x] in s2)) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> t == s1 // hint: don't use addToSet in your code -- use t + [s1[i]] instead
{
  t := [];
  for i := 0 to |s1|
    invariant isSet(t)
    invariant |t| <= i
    invariant forall x :: x in t <==> (x in s1[..i] && x !in s2)
    invariant isEvenSet(s1) && isOddSet(s2) ==> t == s1[..i]
  {
    if s1[i] !in s2 {
      t := t + [s1[i]];
    } else {
      if isEvenSet(s1) && isOddSet(s2) {
        assert s1[i] in s1;
        NotEvenANDOdd(s1[i]);
        assert false;
      }
    }
    assert s1[..i + 1] == s1[..i] + [s1[i]];
  }

  forall k | 0 <= k < |t|
    ensures t[k] in s1 && t[k] !in s2
  {
    assert t[k] in t;
  }
}

/* multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> exists i :: 0<= i < |s| && t[x] == s[i] * n)
  ensures forall x :: (0 <= x < |s| ==> s[x] * n in t)
  ensures isEvenSet(s) || isEven(n) ==> isEvenSet(t)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(t)
{
  t := [];
  for i := 0 to |s|
    invariant isSet(t)
    invariant forall k :: 0 <= k < |t| ==> exists j :: 0 <= j < |s| && t[k] == s[j] * n
    invariant forall y :: y in s[..i] ==> y * n in t
    invariant isEvenSet(s) || isEven(n) ==> isEvenSet(t)
    invariant isOddSet(s) && isOdd(n) ==> isOddSet(t)
  {
    assert s[i] in s;
    EvenTimes(s[i], n);
    OddTimesOdd(s[i], n);
    t := addToSet(t, s[i] * n);
  }
}

method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: x in t ==> exists i1, j1 :: 0<= i1 < |s1| && 0<= j1 < |s2| && x == s1[i1] * s2[j1]
  ensures forall i1, j1 :: i1 in s1 && j1 in s2 ==> i1 * j1 in t
  ensures isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{
  t := [];
  for i := 0 to |s1|
    invariant isSet(t)
    invariant forall x :: x in t ==>
      exists a, b :: 0 <= a < |s1| && 0 <= b < |s2| && x == s1[a] * s2[b]
    invariant forall a, b :: a in s1[..i] && b in s2 ==> a * b in t
    invariant isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
    invariant isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
  {
    assert s1[i] in s1;
    var row := setScale(s2, s1[i]);
    ghost var previous := t;
    t := union(t, row);
    assert s1[..i + 1] == s1[..i] + [s1[i]];
    assert forall x :: x in previous || x in row ==> x in t;
    assert forall b :: b in s2 ==> s1[i] * b in row;
  }
}


/* converts an even set to an odd set by inverting the parity of each element  */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
  requires isEvenSet(s) || isOddSet(s)
  ensures isEvenSet(s) ==> isOddSet(t)
  ensures isOddSet(s) ==> isEvenSet(t)
  ensures |t| == |s|
  ensures forall i :: 0 <= i < |s| ==> t[i] == invertParity(s[i])
{
  t := seq(|s|, i requires 0 <= i < |s| => invertParity(s[i]));

  forall i | 0 <= i < |s|
    ensures isEvenSet(s) ==> isOdd(t[i])
    ensures isOddSet(s) ==> isEven(t[i])
  {
    assert s[i] in s;
    InvertParityCorrect(s[i]);
  }
}
