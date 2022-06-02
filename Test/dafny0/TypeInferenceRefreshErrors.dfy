// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Frames {
  class C {
    var x: int
    var y: int
  }

  // The following was accepted by the old type checking, but it caused a crash in the
  // translator. Now, we disallow it.
  function ToC(): C
  function RegressionTest(): int
    reads ToC // error: type not allowed: () -> C

  function ToSetReal(): set<real>
  function ToMap(): map<object, object>
  function F(r: real, s: set<real>): int
    reads r // error: not a reference type
    reads s // error: not a collection of reference type
    reads ToSetReal // error: not a function to a collection of reference type
    reads ToMap // error: not a function to a collection of reference type
}

module As {
  class C { }
  class D { }
  method M(c: C, d: D, obj: object) {
    var cc: C;
    var dd: D;
    cc := obj as C;
    dd := obj as D;
    cc := d as C; // error: incompatible types
    dd := c as D; // error: incompatible types
  }
}

module Underspecification0 {
  method P() {
    var u;
    var w := !u; // error: type is underspecified
  }
}

module Underspecification1 {
  class E<T> { }

  /* SOON
  method M(obj: object) {
    var ee := obj as E; // error: type parameter of E is underspecified
    assert (obj as E) == (obj as E); // error: type parameter of E is underspecified
    assert (obj as E) == (obj as E<set>); // error: type parameter of set is underspecified
    assert (obj as E) == (obj as E<set<int>>);
  }
  */
}

module Underspecification2 {
  method Q(m: map, n: map) { // fine, because of type-parameter elision rules
    var o := m + n;
  }

  method R() {
    var m: map; // error: type is underspecified
    var n: map; // error: type is underspecified
    var o; // error: type is underspecified
    o := m + n; // error: type of + is underspecified
  }
}
