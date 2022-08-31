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

    public override string ToString() => Decl.Name + ArgumentsToString();

    public SubsetTypeImprovementValue(SubsetTypeDecl decl, [CanBeNull] List<TypeImprovementValue> arguments = null)
    : base(arguments) {
      Decl = decl;
    }
  }

  public class SubsetTypeImprover : TypeImprover {
    public SubsetTypeImprover(Resolver resolver)
      : base(resolver) {
    }

    [CanBeNull]
    public override TypeImprovementValue FromUserProvidedType(Type type) {
      type = type.NormalizeExpandKeepConstraints();
      if (type is UserDefinedType udt && udt.ResolvedClass is SubsetTypeDecl subsetTypeDecl) {
        if (type.TypeArgs.Count == 0) {
          return new SubsetTypeImprovementValue(subsetTypeDecl);
        } else {
          return new SubsetTypeImprovementValue(subsetTypeDecl, type.TypeArgs.ConvertAll(FromUserProvidedType));
        }
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
