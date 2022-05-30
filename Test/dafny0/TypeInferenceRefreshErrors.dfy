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
