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

    /// <summary>
    /// Solves or simplifies as many type constraints as possible.
    /// If "allowDecisions" is "false", then no decisions, only determined inferences, are made; this mode is
    /// appropriate for the partial solving that's done before a member lookup.
    /// Returns "true" if anything changed (that is, if any of the constraints in the type-inference state
    /// caused a change some pre-type proxy).
    /// </summary>
    void PartiallySolveTypeConstraints(string printableContext = null) {
      if (printableContext != null) {
        PrintTypeInferenceState("(partial) " + printableContext);
      }
      bool anythingChanged;
      do {
        anythingChanged = false;
        anythingChanged |= ApplySubtypeConstraints();
        anythingChanged |= ApplyComparableConstraints();
        anythingChanged |= ApplyGuardedConstraints();
      } while (anythingChanged);
    }

    void SolveAllTypeConstraints(string printableContext) {
      PrintTypeInferenceState(printableContext);
      PartiallySolveTypeConstraints(null);
      if (ApplyDefaultAdvice()) {
        PartiallySolveTypeConstraints(null);
      }
      PrintLegend();
      ConfirmTypeConstraints();
      ClearState();
    }

    void ClearState() {
      subtypeConstraints.Clear();
      comparableConstraints.Clear();
      guardedConstraints.Clear();
      defaultAdvice.Clear();
      confirmations.Clear();
      allPreTypeProxies.Clear();
    }

    public void PrintTypeInferenceState(string/*?*/ header = null) {
      Console.WriteLine("*** Type inference state ***{0}", header == null ? "" : $" {header} ");
      PrintList("Subtype constraints", subtypeConstraints, stc => {
        return $"{stc.Super} :> {stc.Sub}";
      });
      PrintList("Comparable constraints", comparableConstraints, cc => {
        return $"{cc.A} ~~ {cc.B}";
      });
      PrintList("Guarded constraints", guardedConstraints, gc => {
        return gc.Kind + Util.Comma("", gc.Arguments, arg => $" {arg}");
      });
      PrintList("Default-type advice", defaultAdvice, advice => {
        return $"{advice.PreType} ~-~-> {advice.WhatString}";
      });
      PrintList("Post-inference confirmations", confirmations, c => {
        return $"{TokToShortLocation(c.tok)}: {c.Check} {c.PreType}: {c.ErrorMessage()}";
      });
    }

    void PrintLegend() {
      PrintList("Legend", allPreTypeProxies, pair => {
        var s = Pad($"?{pair.Item1.UniqueId}", 4) + pair.Item1;
        return pair.Item2 == null ? s : $"{Pad(s, 20)}  {pair.Item2}";
      });
    }

    public static string TokToShortLocation(IToken tok) {
      return $"{System.IO.Path.GetFileName(tok.filename)}({tok.line},{tok.col})";
    }

    void PrintList<T>(string rubric, List<T> list, Func<T, string> formatter) {
      Console.WriteLine($"    {rubric}:");
      foreach (var t in list) {
        var info = $"        {formatter(t)}";
        if (t is PreTypeStateWithErrorMessage preTypeStateWithErrorMessage && !(preTypeStateWithErrorMessage is Confirmation)) {
          info = $"{Pad(info, 30)}  {TokToShortLocation(preTypeStateWithErrorMessage.tok)}: {preTypeStateWithErrorMessage.ErrorMessage()}";
        }
        Console.WriteLine(info);
      }
    }

    string Pad(string s, int minWidth) {
      Contract.Requires(s != null);
      return s + new string(' ', Math.Max(minWidth - s.Length, 0));
    }

    // ---------------------------------------- Equality constraints ----------------------------------------

    void AddEqualityConstraint(PreType a, PreType b, IToken tok, string msgFormat) {
      a = a.Normalize();
      b = b.Normalize();
      if (a == b) {
        // we're already there
      } else if (a is PreTypeProxy pa && !Occurs(pa, b)) {
        pa.Set(b);
      } else if (b is PreTypeProxy pb && !Occurs(pb, a)) {
        pb.Set(a);
      } else if (a is DPreType da && b is DPreType db && da.Decl == db.Decl) {
        Contract.Assert(da.Arguments.Count == db.Arguments.Count);
        for (var i = 0; i < da.Arguments.Count; i++) {
          // TODO: should the error message in the following line be more specific?
          AddEqualityConstraint(da.Arguments[i], db.Arguments[i], tok, msgFormat);
        }
      } else {
        ReportError(tok, msgFormat, a, b);
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

    // ---------------------------------------- State with error message ----------------------------------------

    abstract class PreTypeStateWithErrorMessage {
      public readonly IToken tok;
      public readonly string ErrorFormatString;

      public abstract string ErrorMessage();

      public PreTypeStateWithErrorMessage(IToken tok, string errorFormatString) {
        Contract.Requires(tok != null);
        Contract.Requires(errorFormatString != null);
        this.tok = tok;
        this.ErrorFormatString = errorFormatString;
      }
    }

    // ---------------------------------------- Subtype constraints ----------------------------------------

    class SubtypeConstraint : PreTypeStateWithErrorMessage {
      public readonly PreType Super;
      public readonly PreType Sub;

      public override string ErrorMessage() {
        return string.Format(ErrorFormatString, Super, Sub);
      }

      public SubtypeConstraint(PreType super, PreType sub, IToken tok, string errorFormatString)
        : base(tok, errorFormatString) {
        Contract.Requires(super != null);
        Contract.Requires(sub != null);
        Contract.Requires(tok != null);
        Contract.Requires(errorFormatString != null);
        Super = super;
        Sub = sub;
      }
    }

    private List<SubtypeConstraint> subtypeConstraints = new();

    void AddSubtypeConstraint(PreType super, PreType sub, IToken tok, string errorFormatString) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatString != null);
      subtypeConstraints.Add(new SubtypeConstraint(super, sub, tok, errorFormatString));
    }

    void AddAssignableConstraint(PreType lhs, PreType rhs, IToken tok, string errMsgFormat) {
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(tok != null);
      Contract.Requires(errMsgFormat != null);
      AddSubtypeConstraint(lhs, rhs, tok, errMsgFormat);
    }

    bool ApplySubtypeConstraints() {
      if (subtypeConstraints.Count == 0) {
        // common special case
        return false;
      }
      var constraints = subtypeConstraints;
      subtypeConstraints = new();
      var anythingChanged = false;
      foreach (var constraint in constraints) {
        var used = false;
        var super = constraint.Super.Normalize();
        var sub = constraint.Sub.Normalize();
        if (super is DPreType ptSuper) {
          if (ptSuper.Decl is TraitDecl) {
            // TODO
          } else {
            // "sub" is constrained to be equal to "super"
            Console.WriteLine($"    DEBUG: converting {super} :> {sub} to equality constraint");
            AddEqualityConstraint(super, sub, constraint.tok, constraint.ErrorFormatString);
            used = true;
          }
        } else if (sub is DPreType ptSub) {
          if (ptSub.HasTraitSupertypes()) {
            // TODO
          } else {
            // "super" is constrained to be equal to "sub"
            Console.WriteLine($"    DEBUG: converting {super} :> {sub} to equality constraint");
            AddEqualityConstraint(super, sub, constraint.tok, constraint.ErrorFormatString);
            used = true;
          }
        } else {
          // both are proxies
        }
        if (used) {
          anythingChanged = true;
        } else {
          subtypeConstraints.Add(constraint);
        }
      }
      return anythingChanged;
    }

    // ---------------------------------------- Comparable constraints ----------------------------------------

    class ComparableConstraint : PreTypeStateWithErrorMessage {
      public readonly PreType A;
      public readonly PreType B;

      public override string ErrorMessage() {
        return string.Format(ErrorFormatString, A, B);
      }

      public ComparableConstraint(PreType a, PreType b, IToken tok, string errorFormatString)
        : base(tok, errorFormatString) {
        Contract.Requires(a != null);
        Contract.Requires(b != null);
        Contract.Requires(tok != null);
        Contract.Requires(errorFormatString != null);
        A = a;
        B = b;
      }
    }

    private List<ComparableConstraint> comparableConstraints = new();

    void AddComparableConstraint(PreType a, PreType b, IToken tok, string errorFormatString) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatString != null);
      comparableConstraints.Add(new ComparableConstraint(a, b, tok, errorFormatString));
    }

    bool ApplyComparableConstraints() {
      // TODO
      return false;
    }

    // ---------------------------------------- Guarded constraints ----------------------------------------

    class GuardedConstraint : PreTypeStateWithErrorMessage {
      public readonly string Kind;
      public readonly PreType[] Arguments;

      public override string ErrorMessage() {
        return string.Format(ErrorFormatString, Arguments);
      }

      public GuardedConstraint(string kind, IToken tok, string errorFormatString, params PreType[] arguments)
        : base(tok, errorFormatString) {
        Contract.Requires(kind != null);
        Contract.Requires(tok != null);
        Contract.Requires(errorFormatString != null);
        Kind = kind;
        Arguments = arguments;
      }
    }

    private List<GuardedConstraint> guardedConstraints = new();

    void AddGuardedConstraint(string kind, IToken tok, string errorFormatString, params PreType[] arguments) {
      Contract.Requires(kind != null);
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatString != null);
      guardedConstraints.Add(new GuardedConstraint(kind, tok, errorFormatString, arguments));
    }

    bool ApplyGuardedConstraints() {
      if (guardedConstraints.Count == 0) {
        // common special case
        return false;
      }
      var constraints = guardedConstraints;
      guardedConstraints = new();
      var anythingChanged = false;
      foreach (var constraint in constraints) {
        var used = false;
        switch (constraint.Kind) {
          case "Innable": {
            // For "Innable x s", if s is known, then:
            // if s == c<a> or s == c<a, b> where c is a collection type, then a :> x, else error.
            Contract.Assert(constraint.Arguments.Length == 2);
            var a0 = constraint.Arguments[0].Normalize();
            var a1 = constraint.Arguments[1];
            var coll = a1.UrAncestor(this).AsCollectionType();
            if (coll != null) {
              Console.WriteLine($"    DEBUG: guard applies: Innable {a0} {a1}");
              AddSubtypeConstraint(coll.Arguments[0], a0, constraint.tok,
                "expecting element type to be assignable to {0} (got {1})");
              used = true;
            } else if (a1.Normalize() is DPreType) {
              // type head is determined and it isn't a collection type
              ReportError(constraint.tok, constraint.ErrorMessage());
              used = true;
            }
            break;
          }
          default:
            Contract.Assert(false); // unexpected case
            throw new cce.UnreachableException();
        }
        if (used) {
          anythingChanged = true;
        } else {
          guardedConstraints.Add(constraint);
        }
      }
      return anythingChanged;
    }

    // ---------------------------------------- Advice ----------------------------------------

    class Advice {
      public readonly PreType PreType;
      public readonly AdviceTarget What;

      public string WhatString => What.ToString().ToLower();

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

    bool ApplyDefaultAdvice() {
      bool anythingChanged = false;
      foreach (var advice in defaultAdvice) {
        var preType = advice.PreType.Normalize();
        if (preType is PreTypeProxy proxy) {
          Console.WriteLine($"    DEBUG: acting on advice, setting {proxy} := {advice.WhatString}");

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
          proxy.Set(target);
          anythingChanged = true;
        }
      }
      return anythingChanged;
    }

    // ---------------------------------------- Post-inference confirmations ----------------------------------------

    class Confirmation : PreTypeStateWithErrorMessage {
      public readonly string Check;
      public readonly PreType PreType;

      public override string ErrorMessage() {
        return string.Format(ErrorFormatString, PreType);
      }

      public Confirmation(string check, PreType preType, IToken tok, string errorFormatString)
        : base(tok, errorFormatString) {
        Contract.Requires(check != null);
        Contract.Requires(preType != null);
        Contract.Requires(tok != null);
        Contract.Requires(errorFormatString != null);
        Check = check;
        PreType = preType;
      }
    }

    private List<Confirmation> confirmations = new();

    void AddConfirmation(string check, PreType preType, IToken tok, string errorFormatString) {
      Contract.Requires(check != null);
      Contract.Requires(preType != null);
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatString != null);
      confirmations.Add(new Confirmation(check, preType, tok, errorFormatString));
    }

    void ConfirmTypeConstraints() {
      foreach (var c in confirmations) {
        var okay = true;
        var preType = c.PreType.Normalize();
        if (preType is PreTypeProxy) {
          okay = false;
        } else {
          var pt = (DPreType)preType;
          var familyDeclName = AncestorDecl(pt.Decl).Name;
          switch (c.Check) {
            case "InIntFamily":
              okay = familyDeclName == "int";
              break;
            case "InRealFamily":
              okay = familyDeclName == "real";
              break;
            case "InBoolFamily":
              okay = familyDeclName == "bool";
              break;
            case "InCharFamily":
              okay = familyDeclName == "char";
              break;
            case "InSeqFamily":
              okay = familyDeclName == "seq";
              break;
            case "IsNullableRefType":
              okay = pt.Decl is ClassDecl && !(pt.Decl is ArrowTypeDecl);
              break;
            case "IntLikeOrBitvector":
              if (familyDeclName == "int") {
                okay = true;
              } else if (familyDeclName.StartsWith("bv")) {
                var bits = familyDeclName.Substring(2);
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
          ReportError(c.tok, c.ErrorMessage());
        }
      }
    }
  }
}