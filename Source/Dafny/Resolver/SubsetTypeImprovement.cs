//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class SubsetTypeImprovementValue : TypeImprovementValue {
    public readonly SubsetTypeDecl Decl;

    public override string ToString() {
      return Decl.Name;
    }

    public SubsetTypeImprovementValue(SubsetTypeDecl decl) {
      Decl = decl;
    }
  }

  public class SubsetTypeImprover : TypeImprover {
    public SubsetTypeImprover(Resolver resolver)
      : base(resolver) {
    }

    [CanBeNull]
    public override TypeImprovementValue FromUserProvidedType(Type type) {
      var decl = type.AsSubsetType;
      if (decl != null) {
        return new SubsetTypeImprovementValue(decl);
      } else {
        return null;
      }
    }

    [CanBeNull]
    public override TypeImprovementValue Join(TypeImprovementValue a, TypeImprovementValue b) {
      var aa = (SubsetTypeImprovementValue)a;
      var bb = (SubsetTypeImprovementValue)b;
      // TODO
      return aa;
    }
  }
}
