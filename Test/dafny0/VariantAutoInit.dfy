// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module VariantAutoInit {
  datatype Unit<+X(0)> = Unit // error: an auto-init type parameter is not allowed to be variant
  {
    method Get() returns (r: X) {
      r := *;
    }
  }

  // Note, if a variant auto-init type parameter were allowed, then the following example is a good one
  // to consider. (See also the more troublesome example in module VariantChoiceFunction below.

  type Seventeen = p: int | p == 17 witness 17
  type Twentyone = p: int | p == 21 witness 21

  method Test() {
    var u: Unit<int> := Unit;
    var a17: Unit<Seventeen> := u;
    var a21: Unit<Twentyone> := u;
    assert u == a17 == a21;

    print u, " ", a17, " ", a21, "\n";

    var m := a17.Get();
    var n := a21.Get();
    assert m == 17 && n == 21;
    print m, " ", n, "\n";
  }

  datatype StarUnit<*X(0)> = StarUnit // error: an auto-init type parameter is not allowed to be variant
  {
    method Get() returns (r: X) {
      r := *;
    }
  }

  datatype MinusUnit<-X(0)> = MinusUnit // error: an auto-init type parameter is not allowed to be variant
  {
    method Get() returns (r: X) {
      r := *;
    }
  }

  datatype NonUnit<X(0)> = NonUnit
  {
    method Get() returns (r: X) {
      r := *;
    }
  }

  datatype BangUnit<!X(0)> = BangUnit
  {
    method Get() returns (r: X) {
      r := *;
    }
  }

  // abstract types

  type AbstractType0<X(0)>
  type AbstractType1<!X(0)>
  type AbstractType2<+X(0)> // error: an auto-init type parameter is not allowed to be variant
  type AbstractType3<*X(0)> // error: an auto-init type parameter is not allowed to be variant
  type AbstractType4<-X(0)> // error: an auto-init type parameter is not allowed to be variant

  type GhostAbstractType0<X(00)>
  type GhostAbstractType1<!X(00)>
  type GhostAbstractType2<+X(00)> // error: an auto-init type parameter is not allowed to be variant
  type GhostAbstractType3<*X(00)> // error: an auto-init type parameter is not allowed to be variant
  type GhostAbstractType4<-X(00)> // error: an auto-init type parameter is not allowed to be variant

  // codatatypes

  codatatype Co0<X(0)> = Value
  codatatype Co1<!X(0)> = Value
  codatatype Co2<+X(0)> = Value // error: an auto-init type parameter is not allowed to be variant
  codatatype Co3<*X(0)> = Value // error: an auto-init type parameter is not allowed to be variant
  codatatype Co4<-X(0)> = Value // error: an auto-init type parameter is not allowed to be variant

  codatatype Go0<X(00)> = Value
  codatatype Go1<!X(00)> = Value
  codatatype Go2<+X(00)> = Value // error: an auto-init type parameter is not allowed to be variant
  codatatype Go3<*X(00)> = Value // error: an auto-init type parameter is not allowed to be variant
  codatatype Go4<-X(00)> = Value // error: an auto-init type parameter is not allowed to be variant
}

module VariantChoiceFunction {
  // The following example shows some possible trouble (depending on one's interpretation) that would
  // occur in the presence of a variant auto-init type parameter.

  datatype Unit<+X(00)> = Unit // error: an auto-init type parameter is not allowed to be variant
  {
    ghost function Gimmie(): X {
      var x: X :| true; x
    }
  }

  type Seventeen = p: int | p == 17 witness 17
  type Twentyone = p: int | p == 21 witness 21

  method Test() {
    var u: Unit<int> := Unit;
    var a17: Unit<Seventeen> := u;
    var a21: Unit<Twentyone> := u;
    assert u == a17 == a21;

    ghost var g := a17.Gimmie();
    ghost var h := a21.Gimmie();
    assert g == 17 && h == 21;
    assert u.Gimmie() == a17.Gimmie() by {
      assert u == a17;
    }
    assert u.Gimmie() == a21.Gimmie() by {
      assert u == a17;
    }
    assert false; // ouch, if this would be provable
  }  
}
