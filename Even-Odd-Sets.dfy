
/*** Even ***/

 ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
// The next three lemmas prove that modulo-based definition is equivalent to existential-based definition
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m; // Hint for Dafny to choose n/2 as witness for the existential in the isEven predicate
	}
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
// Useful lemma that may be used later
// It shows that the product of two integers is even if at least one of them is even
lemma EvenTimesAny(n1: int, n2: int)
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
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}
lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{ // TODO: complete his proof
  if n % 2 != 0 {
	  var m := n / 2;
	  assert n == 2 * m + 1; 
	}
}
lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{ // TODO: complete his proof
  OddModulo(n);
	ModuloOdd(n);
}
lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{ // TODO
  if isOdd(n1) && isOdd(n2) {
    var m1: int :| n1 == 2 * m1 + 1;
    var m2: int :| n2 == 2 * m2 + 1;

    // n1*n2 = 4*m1*m2 + 2*m1 + 2*m2 + 1 = 2*(2 * m1 * m2 + m1 + m2) + 1
    var m := 2 * m1 * m2 + m1 + m2; 

    assert n1 * n2 == 2 * m + 1;
    assert isOdd(n1 * n2);
  }
}

/*** Even & Odd ***/

lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{ 
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{ // TODO: complete this proof
  if n % 2 == 0 {
    var m := n / 2;
    assert n == 2 * m;
    assert isEven(n);
  } else {
    var m := n / 2;
    assert n == 2 * m + 1;
    assert isOdd(n);
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{ // TODO: complete this proof
  if isEven(n) {
    var m: int :| n == 2 * m;
    assert invertParity(n) == 2 * m + 1;
    assert isOdd(invertParity(n));
  }

  if isOdd(n) {
    var m: int :| n == 2 * m + 1;
    assert invertParity(n) == 2 * (m + 1);
    assert isEven(invertParity(n));
  }
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
 // TODO: complete this predicate
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// hint don't use return statements. Set b instead.
// method checkSet(s: seq<int>) returns (b: bool)
//   ensures b <==> isSet(s)
// { // TODO: complete this method
// }

/* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
 // TODO: complete this predicate
  forall i :: 0 <= i < |s| ==> s[i] % 2 == 0
} 

// method checkEvenSet(s: seq<int>) returns (b: bool)
//   ensures b <==> isEvenSet(s)
// { // TODO: complete this method
// }

/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  // TODO: complete this predicate
  forall i :: 0 <= i < |s| ==> s[i] % 2 != 0
}

// method checkOddSet(s: seq<int>) returns (b: bool)
//   ensures b <==> isOddSet(s)
// { // TODO: complete this method
// }

/*** Set Operations ***/

// For the following methods specify their behaviour so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
// Marks will be awarded for specifying as much as possible all relevant properties of the output.

/* Adds n to a set s, making sure it remains a set */
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
  // Marks will be awarded for specifying as much as possible all relevant properties of the output.
  // Hint: You don't need to reimplement addToSet as a function to use in your specification.
  requires isSet(s)
  ensures isSet(b)
  ensures n in b
  ensures forall x :: x in b <==> (x in s || x == n)
{ // TODO: Implement the method
  if n in s {
    b := s;
  } else {
    b := s + [n];
  }
}

/* Unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s1)
  requires isSet(s2)
  ensures isSet(t)
  ensures forall x: int :: x in t <==> (x in s1 || x in s2)
{ // TODO: Implement the method
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

/* Intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s1)
  requires isSet(s2)
  ensures isSet(t)
  ensures forall x: int :: x in t <==> (x in s1 && x in s2)
  ensures |t| <= |s1|
{ // TODO: Implement the method
  t := [];

  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant |t| <= i
    invariant forall x: int ::
      x in t <==> (x in s1[..i] && x in s2)
  {
    if s1[i] in s2 {
      t := t + [s1[i]];
    }
  }
}

/* Difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s1)
  requires isSet(s2)
  ensures isSet(t)
  ensures forall x: int :: x in t <==> (x in s1 && x !in s2)
  ensures |t| <= |s1|
{ // TODO: Implement the method
   t := [];

  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant |t| <= i
    invariant forall x: int ::
      x in t <==> (x in s1[..i] && x !in s2)
  {
    if s1[i] !in s2 {
      t := t + [s1[i]];
    }
  }
}

/* Multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: x in t ==>
    exists y :: y in s && x == y * n
  ensures forall x :: x in s ==> x * n in t
{ // TODO: Implement the method
  t := [];

  for i := 0 to |s|
  invariant isSet(t)
  invariant forall x :: x in t ==>
    exists y :: y in s && x == y * n
  invariant forall y :: y in s[..i] ==> y * n in t
  {
  assert s[i] in s;
  assert exists y :: y in s && s[i] * n == y * n;
  t := addToSet(t, s[i] * n);
  }
}

/* Computes the product set of two sets s1 and s2, returning a new set t = { n * m | n in s1, m in s2 }  */
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s1)
  requires isSet(s2)
  ensures isSet(t)
  ensures forall x :: x in t ==>
    exists n, m :: n in s1 && m in s2 && x == n * m
  ensures forall n, m :: n in s1 && m in s2 ==> n * m in t
{ // TODO: Implement the method
t := [];

  for i := 0 to |s1|
    invariant isSet(t)
    invariant forall x :: x in t ==>
      exists a, b :: a in s1 && b in s2 && x == a * b
    invariant forall a, b ::
      a in s1[..i] && b in s2 ==> a * b in t
  {
    for j := 0 to |s2|
      invariant isSet(t)
      invariant forall x :: x in t ==>
        exists a, b :: a in s1 && b in s2 && x == a * b
      invariant forall a, b ::
        a in s1[..i] && b in s2 ==> a * b in t
      invariant forall b ::
        b in s2[..j] ==> s1[i] * b in t
    {
      assert s1[i] in s1 && s2[j] in s2;
      assert exists a, b ::
        a in s1 && b in s2 && s1[i] * s2[j] == a * b;

      t := addToSet(t, s1[i] * s2[j]);
    }
  }
}

/* Converts an even set to an odd set by inverting the parity of each element  
   Hint: Use the invertParity function */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: x in t ==>
    exists y :: y in s && x == y + 1
  ensures forall x :: x in s ==> x + 1 in t
{ // TODO: Implement the method
  t := [];

  for i := 0 to |s|
    invariant isSet(t)
    invariant forall x :: x in t ==>
      exists y :: y in s && x == y + 1
    invariant forall y {:trigger y + 1 in t} ::
      y in s[..i] ==> y + 1 in t
  {
    assert invertParity(s[i]) == s[i] + 1;
    assert s[i] in s;
    assert exists y ::
      y in s && invertParity(s[i]) == y + 1;

    t := addToSet(t, invertParity(s[i]));

  }
}

method Main() {
  print isSet([1, 2, 3]), "\n";
  print isSet([1, 2, 1]), "\n";
}