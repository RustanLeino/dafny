// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Color = BlueX | WhiteX | PastelX
{
  predicate IsFailure() {
    WhiteX? || BlueX?
  }
  function PropagateFailure(): int {
    15
  }
  function Extract(): real {
    if BlueX? then 3.09 else 9.03
  }
}

function method FxF(x: int): bool

method CallF0() {
  var b0 := FxF(15);
  var f: int -> bool := FxF;
  var b1 := f(15);
  assert b0 == b1;
}

method CallF1() {
  var b0 := FxF(15);
  var f := FxF;
  var b1 := f(15);
  assert b0 == b1;
}

class ClassForOld {
  var u: int
  method Old()
    modifies this
  {
    u := u + 1;
    assert old(u) == u - 1;
    if old(u) == 5 {
      var g := 10;
    }
  }
  method Unchanged() {
    assert unchanged(this);
  }
  method New(a': array<int>) returns (r: ClassForOld, a: array<int>)
    ensures fresh(r)
    ensures !fresh(a)
    ensures !fresh(var o := null; o)
    ensures !fresh(null)
  {
    var m := var o := null; o;
    r := new ClassForOld;
    a := a';
  }
}

method ToMultiset(s: set<int>, q: seq<real>) {
  var r0 := multiset(s);
  var r1 := multiset(q);
}

method CreateLambdaAndSequence() {
  var f := i => 2 * i;
  var s := seq(15, f); 
}

datatype Colors = Blue | Yellow | Gray(n: nat)
{
  method PrintMe() {
    if (this == Blue) {
      print "blue";
    } else if (this == Yellow) {
      print "yellow";
    } else {
      print "gray ", n;
    }
    print "\n";
  }
}

module A {
  type T
  datatype BaseType = BaseType(t: T)

  predicate P(d: BaseType)

  class XYZ {
    static predicate ABC(d: BaseType)
  }

  type SubsetType = d: BaseType | P(d)
    witness *
  type SubsetType' = d: BaseType | d == d
    witness *
  type SubsetType'' = d: BaseType | XYZ.ABC(d)
    witness *

  method M0(dp: SubsetType, tt: T) {
    var dp0: SubsetType := [dp][0];
    var dp': SubsetType := dp0.(t := tt); // error: does not satisfy SubsetType
  }

  method M1(dp: SubsetType, tt: T) {
    var dp0 := [dp][0];
    var dp': SubsetType := dp0.(t := tt); // error: does not satisfy SubsetType
  }
}

method Bv() {
  var bv: bv6 := 8;
  var o: ORDINAL := 8;
}
method SUpdate(s: seq<real>, m0: map<real, bool>, m1: imap<real, bool>, mm: multiset<bv6>)
  requires |s| == 10
{
  var s' := s[6 := 3.2];
  var m0' := m0[3.2 := true];
  var m1' := m1[3.2 := true];
  var mm' := mm[8 := 100];
}

method MultiDimArray(m: array3<real>)
  requires m.Length0 == m.Length1 == m.Length2 == 10
{
  var r := m[2, 4, 6];
  var b := r == 2.7;
}

method LittleArray(a: array<real>)
  requires 10 <= a.Length
{
  var s := a [2..3];
}
function Qf(x: int, a: array<int>): bool
  requires x <= a.Length
  reads a
{
  var m := map[2 := true, 3 := false, 4 := false];
  var u := m[3];
  var v := true;
  var w := m[3] == true;
  var ww := u == v;
  forall i :: 0 <= i < x ==> m[i] == true // error: domain
}

trait AsTr { }
class AsCl extends AsTr { }

method Is(clIn: AsCl) {
  var b;
  b := clIn is AsTr;
  b := clIn is object;
  b := clIn is AsCl?;
  b := clIn is AsTr?;
  b := clIn is object?;
}

method As(clIn: AsCl, ch: char) returns (cl: AsCl) {
  var tr: AsTr;
  var obj: object;
  tr := clIn as AsTr;
  obj := clIn as AsTr;
  obj := clIn as object;
  cl := tr as AsCl;
  cl := obj as AsCl;

  var x: int;
  var ord: ORDINAL;
  x := ch as int;
  ord := ch as ORDINAL;
}

method As?(clIn: AsCl) returns (cl: AsCl?) {
  var tr: AsTr?;
  var obj: object?;
  tr := clIn as AsTr?;
  obj := clIn as AsTr?;
  obj := clIn as object?;
  cl := tr as AsCl?;
  cl := obj as AsCl?;
}

datatype BlackWhite = White | Gray(int)

method Dtv(b: bool) returns (c: BlackWhite) {
  var d := White;
  var e := BlackWhite.Gray(15);
  c := if b then BlackWhite.Gray(10) else BlackWhite.Gray(20);
  assert c.Gray?;
}

newtype XX = y: YY | true
type YY = z: int | true
type ZZ = y: YY | true

newtype jnt8 = x |
  var lo := -0x80;
  var hi := 0x80;
  lo <= x < hi

newtype int8 = x |
  - 0x80 <= x < 0x80

method TooBigDiv(a: int8) {
  var b := a;
  var u := false;
  u := !u;
  var q := a != 0;
  var k :=
    var xyz := 3; xyz;
  var l := 3 + if u then 2 else 1;
  
  if
  case true =>
    var x := a / (0-1);  // error: result may not be an int8 (if a is -128)
  case true =>
    var minusOne := -1;
    var y := a % minusOne;  // fine
  case a != 0 =>
    var z := (0-1) % a;  // fine
}

method Good(a: int8)
  requires a != -127-1
{
  var x := a / -1;  // fine
}

class Global {
  static function G(x: int): int { x+x }
  static method N(ghost x: int, g: Global) returns (ghost r: int)
    ensures r == Global.G(x)
  {
    if
    case true =>
      r := G(x);
    case true =>
      r := G(x+0);
    case true =>
      r := g.G(x);
    case true =>
      var g: Global? := null;
      r := g.G(x);
    case true =>
      r := Global.G(x);
  }
}

method Mxy(x: int, y: int) {
  var b := x == y;
  var m, n;
  b := m == n;
  n := 'n';
}

module Inheritance {
  trait Trait { }
  class A extends Trait { }
  class B extends Trait { }
  class C<X, Y, Z> extends Trait { }
  class D<X(0)> {
    var x: X
    var y: X
  }
  class Cell {
    var data: int
  }

  method FInt() returns (r: int) {
    var d := new D;
    var u: int := d.x;
    r := d.y;
  }
  method FIntCell() returns (r: int) {
    var c := new Cell;
    var u := c.data;
    r := u;
  }
  method FCell(c: Cell) {
    var x := c.data;
  }

  method S0(o: object, t: Trait, a: A, b: B)
  {
    var oo := o;
    var x := t;
    var y := a;
  }

  method S1(o: object, t: Trait, a: A, b: B)
  {
    var z := a;
    z := a;
    z := b;
    z := t;
    z := o;
  }

  method S2(o: object, t: Trait, a: A, b: B)
  {
    var uu := a;
  }

  method S3(o: object?, t: Trait?, a: A?, b: B?, c: C?<int, bool, Trait?>) returns (aa: A?, c3: C?<bool, int, Trait?>)
  {
    var uu;
    aa := uu;
    var uu3;
    c3 := uu3;
  }

  method S4(o: object?, t: Trait?, a: A?, b: B?, c: C?<int, bool, Trait?>) returns (aa: A?, c3: C?<bool, int, Trait?>)
  {
    var n := null;
  }

  method S6(o: object?, t: Trait?, a: A?, b: B?, c: C?<int, bool, Trait?>) returns (aa: A?, c3: C?<bool, int, Trait?>)
  {
    var oo := o;
    var tt := t;
    tt := null;
    var a3 := a;
  }
}

newtype MyInt = int

type MyNatSynonym = nat

function F(x: int): int {
  5
}

function G(x: int): int {
  x
}

function H(x: int): int {
  x % 5
}

function I(x: MyInt): MyInt {
  x % 5
}

method M(x: int, m: MyInt, n: nat, n': MyNatSynonym) {
  var y, z, w, q;
  y := x;
  w := 2;
  w := x;
  z := x;
  q := 3;
  q := m;
  y := n;
  y := n';
}

method A0(s: seq<int>) {
  var t;
  t := s;
  var u;
  u := [2, 3];
  var m := map[3 := true];
}

method A1(k: MyInt) {
  var g, h;
  var p := map[g := 3, true := h];
  h := k;
}

method A2() {
  var g;
  var s := [g];
  g := true;
}

method A3() {
  var u;
  u := [2, 3];
  var v := [];
  var b := 2 in v;
}

method B0() {
  var a := true;
  var b;
  var c := b ==> a;
  var d := (a || a) <== b && (a <==> c);
}

method MMap() {
  var a: map<int, bool>, b;
  var c := a - b;
}

function Qfx(a: map<int, real>): int
  requires 3 in a.Keys
{
  var w := a[3] == 3.14;
  17
}

class XyzClass {
  method New(c: XyzClass', b: bool, r': XyzClass) returns (r: XyzClass)
    ensures var q := if b then r else c; true
  {
    r := r';
  }
}
type XyzClass' = c: XyzClass? | true witness *

function {:opaque} OpaqueFunction(): int { 12 }

method Reveal() {
  assert A: true;
  reveal A;
  reveal OpaqueFunction();
}

lemma Calc(a: bool, b: bool, c: int, d: int, e: int)
  requires c <= d <= e
  requires a
  requires b ==> e <= c
  requires B: b
  ensures e <= d
{
  calc ==> {
    a;
    c <= d;
  ==  { reveal B; }
    e <= d;
  }
}

module ToBeRefined {
  method M() {
  }
}
module RefinementDoneHere refines ToBeRefined {
  method M() {
    ...;
  }
}

class CellToModify {
  var data: int
}

method Modify(b: bool) {
  var c := new CellToModify;
  modify c;
  modify c {
    if b {
      c.data := 20;
    }
  }
}

module Patterns {
  datatype Color = Red | Gray(n: nat)

  method VarPattern(c: Color) returns (x: int) {
    if c != Red {
      var Gray(mm) := c;
      x := mm;
    }
  }

  method M(c: Color) returns (x: int) {
    match c
    case Red =>
    case Gray(oo) => x := oo;
  }

  function LetPattern(c: Color): int {
    if c == Red then 3 else
      var Gray(pp) := c;
      pp
  }

  function F(c: Color): int {
    match c
    case Red => 3
    case Gray(oo) => oo
  }
}

/****************************************************************************************
 ******** TO DO *************************************************************************
 ****************************************************************************************
// ------------------
// https://github.com/dafny-lang/dafny/issues/2134
/*
newtype A = b | P(b)
newtype B = a: A | true

predicate P(b: B)
*/

// ------------------
// There was never a test for the error message that comes out here:

datatype Color = White | Gray(int)
datatype ParametricColor<X, Y> = Blue | Red(X) | Green(Y)

method DatatypeValues() {
  var w := White<int>; // error (no hint, since the datatype doesn't take any type parameters)
  var b := Blue<int>; // error: with hint (since the datatype takes _some_ number of type parameters)
  var g := Gray<int>(2);
  var r := Red<int>(3);
}

// ------------------
// Clement suggested the following problem to try through the new type inference.
// On 5 April 2022, he said:

// Below is a test for your new type inference.  Let me know if you would like me to post it as an issue.
// 
// In brief, we have no way today to specify the return type of a lambda: it’s always inferred.  This results in issues like below:
 
function method {:opaque} MaxF<T>(f: T ~> int, ts: seq<T>, default: int) : (m: int)
  reads f.reads
  requires forall t | t in ts :: f.requires(t)
  requires forall t | t in ts :: default <= f(t)
  ensures if ts == [] then m == default else exists t | t in ts :: f(t) == m
  ensures forall t | t in ts :: f(t) <= m
  ensures default <= m
 
datatype Tree =
  | Leaf(i: int)
  | Branch(trs: seq<Tree>)
{
  function method Depth() : nat {
    match this {
      case Leaf(_) => 0
      case Branch(trs) =>
        // var fn : Tree --> nat := (t: Tree) requires t in trs => t.Depth();
        1 + MaxF((t: Tree) requires t in trs => t.Depth(), trs, 0)
    }
  }
}
 
// Dafny rejects the call to MaxF, claiming that forall t | t in ts :: default <= f(t) might not hold.  But default is 0 and f(t)
// has type nat, so it should hold — and in fact just uncommenting the definition of fn above solves the issue… even if fn isn’t used.
 


// ------------------
// Can the following example (from Sean) be improved to not need the explicit seq32<Principal> type annotations?

type seq32<X> = s: seq<X> | |s| < 0x8000_0000
function method seqSize<X>(s: seq32<X>): nat32 {
  |s|
}
type nat32 = x: int | 0 <= x < 0x8000_0000

type Context
type Principal
datatype Option<X> = None | Some(val: X)

class Sean {
  function method principalFromContext(c: Context): Option<Principal>

  function principalsFromContexts(ctxs: seq32<Context>): (res: Option<seq32<Principal>>)
    ensures res.Some? ==> |ctxs| == |res.val|
    ensures res.Some? ==> forall i :: 0 <= i < |ctxs| ==> principalFromContext(ctxs[i]).Some?;
    ensures res.Some? ==> forall i:: 0 <= i < |ctxs| ==> res.val[i] == principalFromContext(ctxs[i]).val
    ensures res.None? ==> exists i :: 0 <= i < |ctxs| && principalFromContext(ctxs[i]).None?
  {
    var empty: seq32<Principal> := [];
    if |ctxs| == 0 then Some(empty) else match principalFromContext(ctxs[0]) {
      case None => None
      case Some(principal) =>
        match principalsFromContexts(ctxs[1..]) {
          case None => None
          case Some(principals) =>
            // TODO: Remove when dafny supports type ascription
            var principals1: seq32<Principal> := [principal] + principals;
            Some(principals1)
        }
    }
  } by method {
    var principals: seq32<Principal> := [];
    for i := 0 to seqSize(ctxs)
      invariant seqSize(principals) == i
      invariant forall j :: 0 <= j < i ==> principalFromContext(ctxs[j]).Some?
      invariant forall j :: 0 <= j < i ==> principals[j] == principalFromContext(ctxs[j]).val
    {
      var principal := principalFromContext(ctxs[i]);
      if principal.None? {
        return None;
      }
      principals := principals + [principal.val];
    }
    assert principals == principalsFromContexts(ctxs).val;
    return Some(principals);
  }
}

// ------------------
// From Clement:

method copy<T>(a: array<T>) returns (a': array<T>) {
  a' := new T[a.Length](k requires k < a.Length reads a => a[k]);
}

// The lambda in a new T is supposed to take a nat, but Dafny infers k to be an int and rejects a[k]

// ------------------
// In this program, one has to write "n + d != 0" instead of "n != -d", because of a previously known problem with type inference

predicate method ge0'(n: int)
  ensures ge0'(n) <==> 0 <= n
{
  downup_search'(n, 0)
}

function method Abs(n: int): nat {
  if n < 0 then -n else n
}

predicate method downup_search'(n: int, d: nat)
  requires d <= Abs(n)
  ensures downup_search'(n, d) <==> d <= n
  decreases Abs(n) - d
{
  n == d || (n + d != 0 && downup_search'(n, d + 1))
  /*
  if n - d == 0 then
    true
  else if n + d == 0 then
    false
  else
    downup_search'(n, d + 1)
  */
}
****************************************************************************************/
