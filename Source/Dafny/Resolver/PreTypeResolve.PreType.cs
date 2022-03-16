//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  public abstract class PreType {
    public PreType Normalize() {
      var t = this;
      while (t is PreTypeProxy proxy && proxy.PT != null) {
        t = proxy.PT;
      }
      return t;
    }

    public abstract bool Same(PreType preType);
  }

  public class PreTypeProxy : PreType {
    public readonly int UniqueId;
    public PreType PT; // filled in by resolution

    public PreTypeProxy(int uniqueId) {
      UniqueId = uniqueId;
    }

    public override string ToString() {
      return PT != null ? PT.ToString() : "?" + UniqueId;
    }

    public override bool Same(PreType preType) {
      return this == preType;
    }

    /// <summary>
    /// Expects PT to be null, and sets PT to the given "target". Assumes that the caller has performed an
    /// occurs check.
    /// </summary>
    public bool Set(PreType target) {
      Contract.Requires(target != null);
      Contract.Requires(PT == null);
      Contract.Assert(PT == null); // make sure we get a run-time check for this important condition
      PT = target;
      return true;
    }
  }

  public class DPreType : PreType {
    public readonly TopLevelDecl Decl;
    public readonly List<PreType> Arguments;

    public DPreType(TopLevelDecl decl, List<PreType> arguments) {
      Decl = decl;
      Arguments = arguments;
    }

    public DPreType(TopLevelDecl decl)
      : this(decl, new()) {
    }

    public override string ToString() {
      var name = Decl.Name;
      if (Arguments.Count == 0) {
        return name;
      }
      return $"{name}<{Util.Comma(Arguments, arg => arg.ToString())}>";
    }

    public override bool Same(PreType preType) {
      if (preType is DPreType that && this.Decl == that.Decl && this.Arguments.Count == that.Arguments.Count) {
        for (var i = 0; i < this.Arguments.Count; i++) {
          if (!this.Arguments[i].Equals(that.Arguments[i])) {
            return false;
          }
        }
        return true;
      }
      return false;
    }

    public bool HasTraitSupertypes() {
      return Decl is TopLevelDeclWithMembers md && md.ParentTraits.Count != 0;
    }
  }
}
