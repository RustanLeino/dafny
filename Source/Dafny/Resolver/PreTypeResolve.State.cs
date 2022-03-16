//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.Runtime.Intrinsics.X86;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public partial class PreTypeResolver {
    // ---------------------------------------- Pre-type inference state ----------------------------------------

    private void ConstrainTypeExprBool(Expression e, string msg) {
      Contract.Requires(e != null);
      Contract.Requires(msg != null);  // expected to have a {0} part
      ConstrainSubtypeRelation(Type.Bool, e.Type, e, msg, e.Type);
    }

    private void ConstrainSubtypeRelation(Type super, Type sub, Expression exprForToken, string msg, params object[] msgArgs) {
      Contract.Requires(sub != null);
      Contract.Requires(super != null);
      Contract.Requires(exprForToken != null);
      Contract.Requires(msg != null);
      Contract.Requires(msgArgs != null);
#if TODO
      return ConstrainSubtypeRelation(super, sub, exprForToken.tok, msg, msgArgs);
#endif
    }

    private void ConstrainSubtypeRelation(PreType super, PreType sub, IToken tok, string msg, params object[] msgArgs) {
      Contract.Requires(sub != null);
      Contract.Requires(super != null);
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(msgArgs != null);
#if TODO
      return ConstrainSubtypeRelation(super, sub, new TypeConstraint.ErrorMsgWithToken(tok, msg, msgArgs));
#endif
    }

    void AddAssignableConstraint(Bpl.IToken tok, Type lhs, Type rhs, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(errMsgFormat != null);
#if TODO
      AddXConstraint(tok, "Assignable", lhs, rhs, errMsgFormat);
#endif
    }

    /// <summary>
    /// Solves or simplifies as many type constraints as possible.
    /// If "allowDecisions" is "false", then no decisions, only determined inferences, are made; this mode is
    /// appropriate for the partial solving that's done before a member lookup.
    /// Returns "true" if anything changed (that is, if any of the constraints in the type-inference state
    /// caused a change some pre-type proxy).
    /// </summary>
    bool PartiallySolveTypeConstraints(string printableContext = null) {
      if (printableContext != null) {
        PrintTypeInferenceState("(partial) " + printableContext);
      }
      var anythingChangedEver = false;
      bool anythingChanged;
      do {
        anythingChanged = false;
        anythingChanged |= ApplySubtypeConstraints();
        anythingChanged |= ApplyComparableConstraints();
        anythingChanged |= ApplyGuardedConstraints();
        anythingChangedEver |= anythingChanged;
      } while (anythingChanged);
      return anythingChangedEver;
    }

    void SolveAllTypeConstraints(string printableContext) {
      PrintTypeInferenceState(printableContext);
      PartiallySolveTypeConstraints(null);
      if (ApplyDefaultAdvice()) {
        PartiallySolveTypeConstraints(null);
      }
      ConfirmTypeConstraints();
      ClearState();
    }

    bool ApplySubtypeConstraints() {
      // TODO
      return false;
    }

    bool ApplyComparableConstraints() {
      // TODO
      return false;
    }

    bool ApplyGuardedConstraints() {
      // TODO
      return false;
    }

    bool ApplyDefaultAdvice() {
      bool anythingChanged = false;
      foreach (var advice in defaultAdvice) {
        var preType = advice.PreType.Normalize();
        if (preType is PreTypeProxy proxy) {
          Console.WriteLine($"    DEBUG: acting on advice, setting {proxy} := {advice.What}");

          Type StringDecl() {
            var s = resolver.moduleInfo.TopLevels["string"];
            return new UserDefinedType(s.tok, s.Name, s, new List<Type>());
          }

          var target = advice.What switch {
            AdviceTarget.Bool => Type2PreType(Type.Bool),
            AdviceTarget.Char => Type2PreType(Type.Char),
            AdviceTarget.Int => Type2PreType(Type.Int),
            AdviceTarget.Real => Type2PreType(Type.Real),
            AdviceTarget.String => Type2PreType(StringDecl()),
          };
          anythingChanged |= proxy.Set(target);
        }
      }
      return anythingChanged;
    }

    void ConfirmTypeConstraints() {
      foreach (var c in confirmations) {
        var okay = true;
        var preType = c.PreType.Normalize();
        if (preType is PreTypeProxy) {
          okay = false;
        } else {
          var pt = (DPreType)preType;
          // TODO: the following should also handle newtype's; this can be done by "normalizing" pt to get to the base of any newtype
          switch (c.Check) {
            case "InIntFamily":
              okay = pt.Decl.Name == "int";
              break;
            case "InRealFamily":
              okay = pt.Decl.Name == "real";
              break;
            case "InBoolFamily":
              okay = pt.Decl.Name == "bool";
              break;
            case "InCharFamily":
              okay = pt.Decl.Name == "char";
              break;
            case "InSeqFamily":
              okay = pt.Decl.Name == "seq";
              break;
            case "IsNullableRefType":
              okay = pt.Decl is ClassDecl && !(pt.Decl is ArrowTypeDecl);
              break;
            case "IntLikeOrBitvector":
              if (pt.Decl.Name == "int") {
                okay = true;
              } else if (pt.Decl.Name.StartsWith("bv")) {
                var bits = pt.Decl.Name.Substring(2);
                okay = bits == "0" || (bits.Length != 0 && bits[0] != '0' && bits.All(ch => '0' <= ch && ch <= '9'));
              } else {
                okay = false;
              }
              break;

            default:
              Contract.Assert(false); // unexpected case
              throw new cce.UnreachableException();
          }
        }
        if (!okay) {
          ReportError(c.Tok, c.ErrorFormat, c.Args);
        }
      }
    }

    void ClearState() {
      subtypeConstraints.Clear();
      comparableConstraints.Clear();
      guardedConstraints.Clear();
      defaultAdvice.Clear();
      confirmations.Clear();
    }

    public void PrintTypeInferenceState(string/*?*/ header = null) {
      Console.WriteLine("*** Type inference state ***{0}", header == null ? "" : $" {header} ");
      PrintList("Subtype constraints", subtypeConstraints, stc => {
        return $"{stc.Super} >: {stc.Sub}";
      });
      PrintList("Comparable constraints", comparableConstraints, cc => {
        return $"{cc.A} ~~ {cc.B}";
      });
      PrintList("Guarded constraints", guardedConstraints, gc => gc.Kind);
      PrintList("Default-type advice", defaultAdvice, advice => {
        return $"{advice.PreType} ~-~-> {advice.What.ToString().ToLower()}";
      });
      PrintList("Post-inference confirmations", confirmations, c => {
        var tok = c.Tok;
        return $"{tok.filename}({tok.line},{tok.col}): {c.Check} {c.PreType}: {string.Format(c.ErrorFormat, c.Args)}";
      });
    }

    void PrintList<T>(string rubric, List<T> list, Func<T, string> formatter) {
      Console.WriteLine($"    {rubric}:");
      foreach (var t in list) {
        Console.WriteLine($"        {formatter(t)}");
      }
    }

    // ---------------------------------------- Equality constraints ----------------------------------------

    void AddEqualityConstraint(PreType a, PreType b, Expression exprForToken, string msgFormat) {
      if (a.Normalize() is PreTypeProxy pa && !Occurs(pa, b)) {
        pa.Set(b);
      } else if (b.Normalize() is PreTypeProxy pb && !Occurs(pb, a)) {
        pb.Set(a);
      } else {
        ReportError(exprForToken, msgFormat, a, b);
      }
    }

    /// <summary>
    /// Returns "true" if "proxy" is among the free variables of "t".
    /// "proxy" is expected to be normalized.
    /// </summary>
    private bool Occurs(PreTypeProxy proxy, PreType t) {
      Contract.Requires(t != null);
      Contract.Requires(proxy != null);
      t = t.Normalize();
      if (t is DPreType pt) {
        return pt.Arguments.Any(arg => Occurs(proxy, arg));
      } else {
        return proxy == t;
      }
    }

    // ---------------------------------------- Subtype constraints ----------------------------------------

    class SubtypeConstraint {
      public readonly PreType Super;
      public readonly PreType Sub;

      public SubtypeConstraint(PreType super, PreType sub) {
        Super = super;
        Sub = sub;
      }
    }

    private List<SubtypeConstraint> subtypeConstraints = new();

    void AddSubtypeConstraint(PreType super, PreType sub) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      subtypeConstraints.Add(new SubtypeConstraint(super, sub));
    }

    // ---------------------------------------- Comparable constraints ----------------------------------------

    class ComparableConstraint {
      public readonly PreType A;
      public readonly PreType B;

      public ComparableConstraint(PreType a, PreType b) {
        A = a;
        B = b;
      }
    }

    private List<ComparableConstraint> comparableConstraints = new();

    void AddComparableConstraint(PreType a, PreType b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      comparableConstraints.Add(new ComparableConstraint(a, b));
    }

    // ---------------------------------------- Guarded constraints ----------------------------------------

    class GuardedConstraint {
      public readonly string Kind;

      public GuardedConstraint(string kind) {
        Kind = kind;
      }
    }

    private List<GuardedConstraint> guardedConstraints = new();

    void AddGuardedConstraint(string kind) {
      Contract.Requires(kind != null);
      guardedConstraints.Add(new GuardedConstraint(kind));
    }

    // ---------------------------------------- Advice ----------------------------------------

    class Advice {
      public readonly PreType PreType;
      public readonly AdviceTarget What;

      public Advice(PreType preType, AdviceTarget advice) {
        PreType = preType;
        What = advice;
      }
    }

    enum AdviceTarget {
      Bool, Char, Int, Real, String
    }

    private List<Advice> defaultAdvice = new();

    void AddDefaultAdvice(PreType preType, AdviceTarget advice) {
      Contract.Requires(preType != null);
      defaultAdvice.Add(new Advice(preType, advice));
    }

    // ---------------------------------------- Post-inference confirmations ----------------------------------------

    class Confirmation {
      public readonly Bpl.IToken Tok;
      public readonly string Check;
      public readonly PreType PreType;
      public readonly string ErrorFormat;
      public readonly object[] Args;

      public Confirmation(Bpl.IToken tok, string check, PreType preType, string errorFormat, params object[] args) {
        Tok = tok;
        Check = check;
        PreType = preType;
        ErrorFormat = errorFormat;
        Args = args;
      }
    }

    private List<Confirmation> confirmations = new();

    void AddConfirmation(Bpl.IToken tok, string check, PreType preType, string errorFormat) {
      confirmations.Add(new Confirmation(tok, check, preType, errorFormat, preType));
    }
  }
}