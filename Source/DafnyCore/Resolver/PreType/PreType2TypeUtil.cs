//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;
using System.Collections.Generic;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public static class PreType2TypeUtil {
  public static Type PreType2Type(PreType preType, bool allowFutureRefinements, TypeParameter.TPVariance futureRefinements) {
    if (allowFutureRefinements) {
      return PreType2RefinableType(preType, futureRefinements);
    } else {
      return PreType2FixedType(preType);
    }
  }

  public static Type PreType2FixedType(PreType preType) {
    return PreType2TypeCore(preType, false, TypeParameter.TPVariance.Co);
  }

  public static Type PreType2RefinableType(PreType preType, TypeParameter.TPVariance futureRefinements) {
    var ty = PreType2TypeCore(preType, true, futureRefinements);
    switch (futureRefinements) {
      case TypeParameter.TPVariance.Co:
        ty = new BottomTypePlaceholder(ty);
        break;
      default:
        break;
    }

    return new TypeRefinementWrapper(ty);
  }

  /// <summary>
  /// The "futureRefinements" parameter is relevant only if "allowFutureRefinements" is "true".
  /// </summary>
  private static Type PreType2TypeCore(PreType preType, bool allowFutureRefinements, TypeParameter.TPVariance futureRefinements) {
    var pt = (DPreType)preType.Normalize(); // all pre-types should have been filled in and resolved to a non-proxy
    if (pt.PrintablePreType != null) {
      pt = pt.PrintablePreType;
    }

    Type ArgumentAsCo(int i) {
      return PreType2Type(pt.Arguments[i], true, futureRefinements);
    }

    switch (pt.Decl.Name) {
      case PreType.TypeNameBool:
        return Type.Bool;
      case PreType.TypeNameChar:
        return Type.Char;
      case PreType.TypeNameInt:
        return Type.Int;
      case PreType.TypeNameReal:
        return Type.Real;
      case PreType.TypeNameORDINAL:
        return Type.BigOrdinal;
      case PreType.TypeNameSet:
        return new SetType(true, ArgumentAsCo(0));
      case PreType.TypeNameIset:
        return new SetType(false, ArgumentAsCo(0));
      case PreType.TypeNameMultiset:
        return new MultiSetType(ArgumentAsCo(0));
      case PreType.TypeNameSeq:
        return new SeqType(ArgumentAsCo(0));
      case PreType.TypeNameMap:
        return new MapType(true, ArgumentAsCo(0), ArgumentAsCo(1));
      case PreType.TypeNameImap:
        return new MapType(false, ArgumentAsCo(0), ArgumentAsCo(1));
      default:
        break;
    }

    var arguments = pt.Arguments.ConvertAll(preType => PreType2RefinableType(preType, futureRefinements));
    if (pt.Decl is ArrowTypeDecl arrowTypeDecl) {
      return new ArrowType(pt.Decl.tok, arrowTypeDecl, arguments);
    } else if (pt.Decl is ValuetypeDecl valuetypeDecl) {
      return valuetypeDecl.CreateType(arguments);
    } else if (pt.Decl is ClassLikeDecl { IsReferenceTypeDecl: true }) {
      return new UserDefinedType(pt.Decl.tok, pt.Decl.Name + "?", pt.Decl, arguments);
    } else {
      return new UserDefinedType(pt.Decl.tok, pt.Decl.Name, pt.Decl, arguments);
    }
  }

  public static void Combine(Type userSuppliedType, PreType preType, bool allowFutureRefinements) {
    var preTypeConverted = PreType2Type(preType, allowFutureRefinements, TypeParameter.TPVariance.Co);
    Combine(userSuppliedType, preTypeConverted);
  }

  /// <summary>
  /// This method combines the respective user-supplied types with the inferred pre-types. It expects that either
  ///     - "types" is null, which represents the case where the types are inferred. In this case, the method returns a new
  ///       list that contains the converted pre-types.
  ///     - "types" is non-null, which represents the case where the user supplied types. In this case, "types" and
  ///       "preTypes" are expected to have the same length. The respective types and pre-types are combined in "types",
  ///       and then "types" is returned.
  /// </summary>
  public static List<Type> Combine([CanBeNull] List<Type> types, List<PreType> preTypes, bool allowFutureRefinements) {
    Contract.Requires(types == null || types.Count == preTypes.Count);
    if (types == null) {
      if (allowFutureRefinements) {
        return preTypes.ConvertAll(preType => PreType2RefinableType(preType, TypeParameter.TPVariance.Co));
      } else {
        return preTypes.ConvertAll(PreType2FixedType);
      }
    }

    Contract.Assert(types.Count == preTypes.Count);
    for (var i = 0; i < types.Count; i++) {
      Combine(types[i], preTypes[i], allowFutureRefinements);
    }
    return types;
  }

  private static void Combine(Type type, Type preTypeConverted) {
    Contract.Requires(type != null);
    Contract.Requires(preTypeConverted != null);

    type = type.NormalizeAndAdjustForScope();
    if (type is TypeProxy { T: null } typeProxy) {
      typeProxy.T = preTypeConverted;
    } else {
      // Even if the head type of preTypeConverted is a refinement wrapper, we're going to stick with the user-defined type, so we Normalize() here.
      preTypeConverted = preTypeConverted.Normalize();

      Contract.Assert((type as UserDefinedType)?.ResolvedClass == (preTypeConverted as UserDefinedType)?.ResolvedClass);
      Contract.Assert(type.TypeArgs.Count == preTypeConverted.TypeArgs.Count);
      for (var i = 0; i < type.TypeArgs.Count; i++) {
        // TODO: the following should take variance into consideration
        Combine(type.TypeArgs[i], preTypeConverted.TypeArgs[i]);
      }
    }
  }

}