//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny {
  public abstract class PreType {
    public PreType Normalize() {
      var t = this;
      while (t is PreTypeProxy proxy && proxy.PT != null) {
        t = proxy.PT;
      }
      return t;
    }

    public static bool Same(PreType a, PreType b) {
      a = a.Normalize();
      b = b.Normalize();
      if (a is DPreType ap && b is DPreType bp && ap.Decl == bp.Decl) {
        Contract.Assert(ap.Arguments.Count == bp.Arguments.Count);
        for (var i = 0; i < ap.Arguments.Count; i++) {
          if (!Same(ap.Arguments[i], bp.Arguments[i])) {
            return false;
          }
        }
        return true;
      }
      return a == b;
    }

    public PreType UrAncestor(PreTypeResolver ptResolver) {
      Contract.Requires(ptResolver != null);
      var pt = this;
      while (true) {
        pt = pt.Normalize();
        if (pt is DPreType preType && preType.Decl is NewtypeDecl newtypeDecl) {
          // expand the newtype into its base type
          var subst = PreTypeSubstMap(newtypeDecl.TypeArgs, preType.Arguments);
          var basePreType = ptResolver.Type2PreType(newtypeDecl.BaseType);
          pt = basePreType.Substitute(subst);
        } else {
          // nothing more we can do
          return pt;
        }
      }
    }

    public DPreType AsCollectionType() {
      if (Normalize() is DPreType dp) {
        switch (dp.Decl.Name) {
          case "set":
          case "iset":
          case "seq":
          case "multiset":
          case "map":
          case "imap":
            return dp;
          default:
            break;
        }
      }
      return null;
    }

    public static Dictionary<TypeParameter, PreType> PreTypeSubstMap(List<TypeParameter> parameters, List<PreType> arguments) {
      Contract.Requires(parameters.Count == arguments.Count);
      var subst = new Dictionary<TypeParameter, PreType>();
      for (var i = 0; i < parameters.Count; i++) {
        subst.Add(parameters[i], arguments[i]);
      }
      return subst;
    }

    /// <summary>
    /// If the substitution has no effect, the return value is pointer-equal to 'this'
    /// </summary>
    public abstract PreType Substitute(Dictionary<TypeParameter, PreType> subst);

    public bool IsLeafType() {
      var t = Normalize();
      if (!(t is DPreType pt)) {
        return false;
      } else if (pt.Decl is TraitDecl) {
        return false;
      }
      // Now, it comes down to the type arguments
      Contract.Assert(pt.Decl.TypeArgs.Count == pt.Arguments.Count);
      for (var i = 0; i < pt.Decl.TypeArgs.Count; i++) {
        switch (pt.Decl.TypeArgs[i].Variance) {
          case TypeParameter.TPVariance.Non:
            // this is fine for a leaf
            break;
          case TypeParameter.TPVariance.Co:
            if (!pt.Arguments[i].IsLeafType()) {
              return false;
            }
            break;
          case TypeParameter.TPVariance.Contra:
            if (!pt.Arguments[i].IsRootType()) {
              return false;
            }
            break;
        }
      }
      return true;
    }

    public bool IsRootType() {
      var t = Normalize();
      if (!(t is DPreType pt)) {
        return false;
      } else if (pt.Decl is TopLevelDeclWithMembers md && md.ParentTraits.Count != 0) {
        return false;
      }
      // Now, it comes down to the type arguments
      Contract.Assert(pt.Decl.TypeArgs.Count == pt.Arguments.Count);
      for (var i = 0; i < pt.Decl.TypeArgs.Count; i++) {
        switch (pt.Decl.TypeArgs[i].Variance) {
          case TypeParameter.TPVariance.Non:
            // this is fine for a root
            break;
          case TypeParameter.TPVariance.Co:
            if (!pt.Arguments[i].IsRootType()) {
              return false;
            }
            break;
          case TypeParameter.TPVariance.Contra:
            if (!pt.Arguments[i].IsLeafType()) {
              return false;
            }
            break;
        }
      }
      return true;
    }
  }

  public class PreTypeProxy : PreType {
    public readonly int UniqueId;
    public PreType PT; // filled in by resolution

    /// <summary>
    /// There should be just one call to this constructor, namely from PreTypeResolver.CreatePreTypeProxy.
    /// Other callers that need a new pre-type proxy should call PreTypeResolver.CreatePreTypeProxy.
    /// </summary>
    public PreTypeProxy(int uniqueId) {
      UniqueId = uniqueId;
    }

    public override string ToString() {
      return PT != null ? PT.ToString() : "?" + UniqueId;
    }

    /// <summary>
    /// Expects PT to be null, and sets PT to the given "target". Assumes that the caller has performed an
    /// occurs check.
    /// </summary>
    public void Set(PreType target) {
      Contract.Requires(target != null);
      Contract.Requires(PT == null);
      Contract.Assert(PT == null); // make sure we get a run-time check for this important condition
      PT = target;
    }

    public override PreType Substitute(Dictionary<TypeParameter, PreType> subst) {
      return this;
    }
  }

  public class DPreType : PreType {
    public readonly TopLevelDecl Decl;
    public readonly List<PreType> Arguments;
    public readonly Type PrintableType;

    public DPreType(TopLevelDecl decl, List<PreType> arguments, Type printableType = null) {
      Decl = decl;
      Arguments = arguments;
      PrintableType = printableType;
    }

    public DPreType(TopLevelDecl decl, PreTypeResolver preTypeResolver, Type printableType = null)
      : this(decl, decl.TypeArgs.ConvertAll(_ => preTypeResolver.CreatePreTypeProxy()), printableType) {
      Contract.Requires(decl != null);
      Contract.Requires(preTypeResolver != null);
    }

    public override string ToString() {
      var name = Decl.Name;
      if (IsReferenceTypeDecl(Decl)) {
        name = name + "?";
      }
      if (Arguments.Count == 0) {
        return name;
      }
      var s = $"{name}<{Util.Comma(Arguments, arg => arg.ToString())}>";
      if (PrintableType != null) {
#if PRINT_SYNONYMS
        s += $"/*aka {PrintableType}*/";
#endif
      }
      return s;
    }

    public bool HasTraitSupertypes() {
      /*
       * When traits can be used as supertypes for non-reference types (and "object" is an implicit parent trait of every
       * class), then this method can be implemented by
       *         return Decl is TopLevelDeclWithMembers md && md.ParentTraits.Count != 0;
       * For now, every reference type except "object" has trait supertypes.
       */
      if (Decl is TraitDecl trait && trait.IsObjectTrait) {
        return false;
      }
      return IsReferenceTypeDecl(Decl);
    }

    public static bool IsReferenceTypeDecl(TopLevelDecl decl) {
      Contract.Requires(decl != null);
      return decl is ClassDecl && !(decl is ArrowTypeDecl);
    }

    public static bool IsArrowType(TopLevelDecl decl) {
      Contract.Requires(decl != null);
      return decl.Name.StartsWith("~>");
    }

    public override PreType Substitute(Dictionary<TypeParameter, PreType> subst) {
      if (Decl is TypeParameter typeParameter) {
        Contract.Assert(Arguments.Count == 0);
        return subst.GetValueOrDefault(typeParameter, this);
      }

      // apply substitutions to arguments
      List<PreType> newArguments = null; // allocate the new list lazily
      for (var i = 0; i < Arguments.Count; i++) {
        var arg = Arguments[i];
        var pt = arg.Substitute(subst);
        if (pt != arg && newArguments == null) {
          // lazily construct newArguments
          newArguments = new();
          // copy all previous items, all of which were unaffected by substitution
          for (var j = 0; j < i; j++) {
            newArguments.Add(Arguments[j]);
          }
        }
        if (newArguments != null) {
          newArguments.Add(pt);
        }
      }

      return newArguments == null ? this : new DPreType(Decl, newArguments);
    }
  }
}
