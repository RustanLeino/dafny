// RUN: %exits-with 1 %baredafny verify %args --function-syntax:2 null.dfy 2> "%t"
// RUN: %diff "%s.expect" "%t"
