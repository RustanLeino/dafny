//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

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
    void PartiallySolveTypeConstraints(string printableContext = null, bool makeDecisions = false) {
      if (printableContext != null) {
        PrintTypeInferenceState("(partial) " + printableContext);
      }
      bool anythingChanged;
      do {
        anythingChanged = false;
        anythingChanged |= ApplySubtypeConstraints();
        anythingChanged |= ApplyComparableConstraints();
        anythingChanged |= ApplyGuardedConstraints();
        if (makeDecisions) {
          if (DecideHeadsFromBounds(true)) {
            anythingChanged = true;
          } else if (DecideHeadsFromBounds(false)) {
            anythingChanged = true;
          }
        }
      } while (anythingChanged);
    }

    void SolveAllTypeConstraints(string printableContext) {
      PrintTypeInferenceState(printableContext);
      PartiallySolveTypeConstraints(null);

      PartiallySolveTypeConstraints(null, true);

      if (ApplyDefaultAdvice()) {
        PartiallySolveTypeConstraints(null, true);
      }

      PrintLegend();
      ConfirmTypeConstraints();
      ClearState();
    }

    void ClearState() {
      unnormalizedSubtypeConstraints.Clear();
      comparableConstraints.Clear();
      guardedConstraints.Clear();
      defaultAdvice.Clear();
      confirmations.Clear();
      allPreTypeProxies.Clear();
    }

    public void PrintTypeInferenceState(string/*?*/ header = null) {
      if (!DafnyOptions.O.NewTypeInferenceDebug) {
        return;
      }
      Console.WriteLine("*** Type inference state ***{0}", header == null ? "" : $" {header} ");
      PrintList("Subtype constraints", unnormalizedSubtypeConstraints, stc => {
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
      return $"{System.IO.Path.GetFileName(tok.filename)}({tok.line},{tok.col - 1})";
    }

    void PrintList<T>(string rubric, List<T> list, Func<T, string> formatter) {
      if (!DafnyOptions.O.NewTypeInferenceDebug) {
        return;
      }
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

    void DebugPrint(string format, params object[] args) {
      if (DafnyOptions.O.NewTypeInferenceDebug) {
        Console.WriteLine(format, args);
      }
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
        Super = super.Normalize();
        Sub = sub.Normalize();
      }

      public SubtypeConstraint Normalize() {
        var super = Super.Normalize();
        var sub = Sub.Normalize();
        if (object.ReferenceEquals(super, Super) && object.ReferenceEquals(sub, Sub)) {
          return this;
        } else {
          return new SubtypeConstraint(super, sub, Token.NoToken, ErrorFormatString);
        }
      }
    }

    private List<SubtypeConstraint> unnormalizedSubtypeConstraints = new();

    void AddSubtypeConstraint(PreType super, PreType sub, IToken tok, string errorFormatString) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      Contract.Requires(tok != null);
      Contract.Requires(errorFormatString != null);
      unnormalizedSubtypeConstraints.Add(new SubtypeConstraint(super, sub, tok, errorFormatString));
    }

    void AddAssignableConstraint(PreType lhs, PreType rhs, IToken tok, string errMsgFormat) {
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(tok != null);
      Contract.Requires(errMsgFormat != null);
      AddSubtypeConstraint(lhs, rhs, tok, errMsgFormat);
    }

    bool ApplySubtypeConstraints() {
      if (unnormalizedSubtypeConstraints.Count == 0) {
        // common special case
        return false;
      }
      var constraints = unnormalizedSubtypeConstraints;
      unnormalizedSubtypeConstraints = new();
      var anythingChanged = false;
      foreach (var constraint in constraints) {
        var used = false;
        var super = constraint.Super.Normalize();
        var sub = constraint.Sub.Normalize();
        var ptSuper = super as DPreType;
        var ptSub = sub as DPreType;
        // In the following explanations, D is assumed to be a type with three
        // type parameters, being co-variant, contra-variant, and non-variant, respectively.
        if (ptSuper != null && ptSub != null) {
          // We're looking at D<a,b,c> :> E<x,y>
          // If E<x,y> can be rewritten as D<f(x,y), g(x,y), h(x,y)>, then
          //     Constrain a :> f(x,y)
          //     Constrain g(x,y) :> b
          //     Constrain c == h(x,y)
          // else report an error
          var arguments = AdaptTypeArgumentsForParent(ptSuper.Decl, ptSub.Decl, ptSub.Arguments);
          if (arguments != null) {
            Contract.Assert(arguments.Count == ptSuper.Decl.TypeArgs.Count);
            ConstrainTypeArguments(ptSuper.Decl.TypeArgs, ptSuper.Arguments, arguments, constraint.tok);
            used = true;
          } else {
            ReportError(constraint.tok, constraint.ErrorMessage());
            used = true;
          }
        } else if (ptSuper != null) {
          // We're looking at D<a,b,c> :> sub
          // If the head of D has no proper subtypes (i.e., it is not a trait), then
          //     Introduce alpha, beta
          //     Constrain sub == D<alpha, beta, c>
          //     Constrain a :> alpha
          //     Constrain beta :> b
          // else do nothing for now
          if (!(ptSuper.Decl is TraitDecl)) {
            var arguments = CreateProxiesForTypesAccordingToVariance(ptSuper.Decl.TypeArgs, ptSuper.Arguments);
            var pt = new DPreType(ptSuper.Decl, arguments);
            AddEqualityConstraint(sub, pt, constraint.tok, constraint.ErrorFormatString);
            used = true;
          }
        } else if (ptSub != null) {
          // We're looking at super :> D<a,b,c>
          // If the head of D has no proper supertypes (i.e., D has no parent traits), then
          //     Introduce alpha, beta
          //     Constrain alpha :> a
          //     Constrain b :> beta
          // else do nothing for now
          if (ptSub.Decl is TopLevelDeclWithMembers md && md.ParentTraits.Count != 0) {
            // there are parent traits
          } else if (ptSub.Decl is ClassDecl cl && !(ptSub.Decl is ArrowTypeDecl) && !cl.IsObjectTrait) {
            // this is a non-object reference type, so it implicitly has "object" as a super-trait
          } else {
            var arguments = CreateProxiesForTypesAccordingToVariance(ptSub.Decl.TypeArgs, ptSub.Arguments);
            var pt = new DPreType(ptSub.Decl, arguments);
            AddEqualityConstraint(pt, super, constraint.tok, constraint.ErrorFormatString);
            used = true;
          }
        } else {
          // do nothing for now
        }
        if (used) {
          anythingChanged = true;
        } else {
          unnormalizedSubtypeConstraints.Add(constraint.Normalize());
        }
      }
      return anythingChanged;
    }

    /// <summary>
    /// If "super" is an ancestor of "sub", then return a list "L" of arguments for "super" such that
    /// "super<L>" is a supertype of "sub<subArguments>".
    /// Otherwise, return "null".
    /// </summary>
    List<PreType> /*?*/ AdaptTypeArgumentsForParent(TopLevelDecl super, TopLevelDecl sub, List<PreType> subArguments) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      Contract.Requires(subArguments != null);
      Contract.Requires(sub.TypeArgs.Count == subArguments.Count);

      if (super == sub) {
        return subArguments;
      } else if (sub is TopLevelDeclWithMembers md) {
        var subst = PreType.PreTypeSubstMap(md.TypeArgs, subArguments);
        foreach (var parentType in md.ParentTraits) {
          var parentPreType = (DPreType)Type2PreType(parentType).Substitute(subst);
          var arguments = AdaptTypeArgumentsForParent(super, parentPreType.Decl, parentPreType.Arguments);
          if (arguments != null) {
            return arguments;
          }
        }
        // If "md" is a reference type, its parents implicitly contain "object", but "object" might not be explicitly included in .ParentTraits.
        // We handle it here.
        if (DPreType.IsReferenceTypeDecl(md)) {
          // "md" is a reference type, so "object" is a parent, and "object" has no type arguments
          return new List<PreType>();
        }
      }
      return null;
    }

    List<PreType> CreateProxiesForTypesAccordingToVariance(List<TypeParameter> parameters, List<PreType> arguments) {
      Contract.Requires(parameters != null);
      Contract.Requires(arguments != null);
      Contract.Requires(parameters.Count == arguments.Count);

      if (parameters.All(tp => tp.Variance == TypeParameter.TPVariance.Non)) {
        // special case this common situation
        return arguments;
      }
      var newArgs = new List<PreType>();
      for (var i = 0; i < parameters.Count; i++) {
        var tp = parameters[i];
        if (tp.Variance == TypeParameter.TPVariance.Non) {
          newArgs.Add(arguments[i]);
        } else {
          var co = tp.Variance == TypeParameter.TPVariance.Co ? "co" : "contra";
          var proxy = CreatePreTypeProxy($"type used in {co}variance constraint");
          newArgs.Add(proxy);
        }
      }
      return newArgs;
    }

    /// <summary>
    /// For every non-variant parameters[i], constrain superArguments[i] == subArguments[i].
    /// For every co-variant parameters[i], constrain superArguments[i] :> subArguments[i].
    /// For every contra-variant parameters[i], constrain subArguments[i] :> superArguments[i].
    /// </summary>
    void ConstrainTypeArguments(List<TypeParameter> parameters, List<PreType> superArguments, List<PreType> subArguments, IToken tok) {
      Contract.Requires(parameters != null);
      Contract.Requires(superArguments != null);
      Contract.Requires(subArguments != null);
      Contract.Requires(parameters.Count == superArguments.Count && superArguments.Count == subArguments.Count);
      Contract.Requires(tok != null);

      for (var i = 0; i < parameters.Count; i++) {
        var tp = parameters[i];
        var arg0 = superArguments[i];
        var arg1 = subArguments[i];
        if (tp.Variance == TypeParameter.TPVariance.Non) {
          AddEqualityConstraint(arg0, arg1, tok, "non-variance would require {0} == {1}");
        } else if (tp.Variance == TypeParameter.TPVariance.Co) {
          AddSubtypeConstraint(arg0, arg1, tok, "covariance would require {0} :> {1}");
        } else {
          AddSubtypeConstraint(arg1, arg0, tok, "contravariance would require {0} :> {1}");
        }
      }
    }

    bool DecideHeadsFromBounds(bool fromSubBounds) {
      // For each proxy, compute the join/meet of its sub/super-bound heads
      Dictionary<PreTypeProxy, TopLevelDecl> candidateHeads = new();
      Dictionary<PreTypeProxy, SubtypeConstraint> constraintOrigins = new();
      foreach (var constraint in unnormalizedSubtypeConstraints) {
        var proxy = (fromSubBounds ? constraint.Super : constraint.Sub).Normalize() as PreTypeProxy;
        var bound = (fromSubBounds ? constraint.Sub : constraint.Super).Normalize() as DPreType;
        if (proxy != null && bound != null) {
          if (!candidateHeads.TryGetValue(proxy, out var previousBest)) {
            candidateHeads.Add(proxy, bound.Decl);
            constraintOrigins.Add(proxy, constraint);
          } else {
            var combined = fromSubBounds ? JoinHeads(previousBest, bound.Decl) : MeetHeads(previousBest, bound.Decl);
            if (combined == null) {
              // the two joins/meets were in conflict with each other; ignore the new one
            } else {
              candidateHeads[proxy] = combined;
            }
          }
        }
      }
      var anythingChanged = false;
      foreach (var (proxy, best) in candidateHeads) {
        var pt = new DPreType(best, best.TypeArgs.ConvertAll(_ => CreatePreTypeProxy()));
        var constraint = constraintOrigins[proxy];
        DebugPrint($"    DEBUG: head decision {proxy} := {pt}");
        AddEqualityConstraint(proxy, pt, constraint.tok, constraint.ErrorFormatString); // TODO: the message could be made more specific now (perhaps)
        anythingChanged = true;
      }
      return anythingChanged;
    }

    TopLevelDecl/*?*/ JoinHeads(TopLevelDecl a, TopLevelDecl b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      var aAncestors = new HashSet<TopLevelDecl>();
      var bAncestors = new HashSet<TopLevelDecl>();
      ComputeAncestors(a, aAncestors);
      ComputeAncestors(b, bAncestors);
      var ancestors = aAncestors.Intersect(bAncestors).ToList();
      // Unless ancestors.Count == 1, there is no unique answer, and not necessary any way to determine the best
      // answer. As a heuristic, pick the element with the highest unique Height number. If there is no such
      // element, return null.
      while (ancestors.Count != 0) {
        var maxAmongAncestors = ancestors.Max(Height);
        var highestAncestors = ancestors.Where(ancestor => Height(ancestor) == maxAmongAncestors).ToList();
        if (highestAncestors.Count == 1) {
          return highestAncestors.ElementAt(0);
        }
        ancestors.RemoveAll(ancestor => Height(ancestor) < maxAmongAncestors);
      }
      return null;
    }

    TopLevelDecl/*?*/ MeetHeads(TopLevelDecl a, TopLevelDecl b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      var aAncestors = new HashSet<TopLevelDecl>();
      if (aAncestors.Contains(b)) {
        // that's good enough; let's pick a
        return a;
      }
      var bAncestors = new HashSet<TopLevelDecl>();
      if (bAncestors.Contains(a)) {
        // that's good enough; let's pick b
        return b;
      }
      // give up
      return null;
    }

    void ComputeAncestors(TopLevelDecl d, ISet<TopLevelDecl> ancestors) {
      if (!ancestors.Contains(d)) {
        ancestors.Add(d);
        if (d is TopLevelDeclWithMembers dm) {
          dm.ParentTraitHeads.Iter(parent => ComputeAncestors(parent, ancestors));
        }
      }
    }

    int Height(TopLevelDecl d) {
      if (d is TopLevelDeclWithMembers md) {
        var maxAmongParents = md.ParentTraitHeads.Count == 0 ? 0 : md.ParentTraitHeads.Max(Height);
        return maxAmongParents + 1;
      } else {
        return 0;
      }
    }

    IEnumerable<DPreType> AllSubBounds(PreTypeProxy proxy, ISet<PreTypeProxy> visited) {
      Contract.Requires(proxy.PT == null);
      if (!visited.Contains(proxy)) {
        visited.Add(proxy);
        foreach (var constraint in unnormalizedSubtypeConstraints) {
          if (constraint.Super.Normalize() == proxy) {
            var sub = constraint.Sub.Normalize();
            if (sub is PreTypeProxy subProxy) {
              foreach (var pt in AllSubBounds(subProxy, visited)) {
                yield return pt;
              }
            } else {
              yield return (DPreType)sub;
            }
          }
        }
      }
    }

    IEnumerable<DPreType> AllSuperBounds(PreTypeProxy proxy, ISet<PreTypeProxy> visited) {
      Contract.Requires(proxy.PT == null);
      if (!visited.Contains(proxy)) {
        visited.Add(proxy);
        foreach (var constraint in unnormalizedSubtypeConstraints) {
          if (constraint.Sub.Normalize() == proxy) {
            var super = constraint.Super.Normalize();
            if (super is PreTypeProxy superProxy) {
              foreach (var pt in AllSuperBounds(superProxy, visited)) {
                yield return pt;
              }
            } else {
              yield return (DPreType)super;
            }
          }
        }
      }
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
      // The meaning of a comparable constraint
      //     A ~~ B
      // is the disjunction
      //     A :> B    or    B :> A
      // To decide between these two possibilities, enough information must be available
      // about A and/or B.
      if (comparableConstraints.Count == 0) {
        // common special case
        return false;
      }
      var constraints = comparableConstraints;
      comparableConstraints = new();
      var anythingChanged = false;
      foreach (var constraint in constraints) {
        var used = false;
        var a = constraint.A.Normalize();
        var b = constraint.B.Normalize();
        var ptA = a as DPreType;
        var ptB = b as DPreType;
        if (ptA != null && ptB != null &&
            AdaptTypeArgumentsForParent(ptB.Decl, ptA.Decl, ptA.Arguments) == null &&
            AdaptTypeArgumentsForParent(ptA.Decl, ptB.Decl, ptB.Arguments) == null) {
          // neither A :> B nor B :> A is possible
          ReportError(constraint.tok, constraint.ErrorMessage());
          used = true;
        } else if ((ptA != null && ptA.IsLeafType()) || (ptB != null && ptB.IsRootType())) {
          // use B :> A
          DebugPrint($"    DEBUG: turning ~~ into {b} :> {a}");
          AddSubtypeConstraint(b, a, constraint.tok, constraint.ErrorFormatString);
          used = true;
        } else if ((ptA != null && ptA.IsRootType()) || (ptB != null && ptB.IsLeafType())) {
          // use A :> B
          DebugPrint($"    DEBUG: turning ~~ into {a} :> {b}");
          AddSubtypeConstraint(a, b, constraint.tok, constraint.ErrorFormatString);
          used = true;
        } else {
          // not enough information to determine
        }
        if (used) {
          anythingChanged = true;
        } else {
          comparableConstraints.Add(constraint);
        }
      }
      return anythingChanged;
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
              DebugPrint($"    DEBUG: guard applies: Innable {a0} {a1}");
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

      public string WhatString => What == AdviceTarget.Object ? "object?" : What.ToString().ToLower();

      public Advice(PreType preType, AdviceTarget advice) {
        PreType = preType;
        What = advice;
      }
    }

    enum AdviceTarget {
      Bool, Char, Int, Real, String, Object
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
          DebugPrint($"    DEBUG: acting on advice, setting {proxy} := {advice.WhatString}");

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
            AdviceTarget.Object => Type2PreType(resolver.builtIns.ObjectQ())
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