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
  }
  
  public class PreTypeResolver {
    private readonly Resolver resolver;
    private readonly Scope<TypeParameter> allTypeParameters = new();
    private readonly Scope<IVariable> scope = new();
    private readonly Scope<Statement> enclosingStatementLabels = new();
    private readonly Scope<Label> dominatingStatementLabels = new();
    
    TopLevelDeclWithMembers currentClass;
    Method currentMethod;
    
    private int ErrorCount => resolver.Reporter.Count(ErrorLevel.Error);

    private void ReportError(Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      ReportError(d.tok, msg, args);
    }
    
    private void ReportError(Expression expr, string msg, params object[] args) {
      Contract.Requires(expr != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      ReportError(expr.tok, msg, args);
    }
    
    private void ReportError(Bpl.IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      resolver.Reporter.Error(MessageSource.Resolver, tok, msg, args);
    }
    
    private void ReportWarning(Bpl.IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      resolver.Reporter.Warning(MessageSource.Resolver, tok, msg, args);
    }

    private readonly Dictionary<string, TopLevelDecl> preTypeBuiltins = new();

    TopLevelDecl BuiltInTypeDecl(string name, int typeParameterCount = 0) {
      Contract.Requires(name != null);
      if (!preTypeBuiltins.TryGetValue(name, out var decl)) {
        decl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, typeParameterCount, _ => false, null);
        preTypeBuiltins.Add(name, decl);
      }
      return decl;
    }

    private int typeProxyCount = 0; // used to give each PreTypeProxy a unique ID

    public PreType CreatePreTypeProxy() {
      return new PreTypeProxy(typeProxyCount++);
    }

    public PreType Type2PreType(Type type) {
      Contract.Requires(type != null);

      type = type.NormalizeExpand();
      if (type is BoolType) {
        return new DPreType(BuiltInTypeDecl("bool"));
      } else if (type is CharType) {
        return new DPreType(BuiltInTypeDecl("char"));
      } else if (type is IntType) {
        return new DPreType(BuiltInTypeDecl("int"));
      } else if (type is RealType) {
        return new DPreType(BuiltInTypeDecl("real"));
      } else if (type is BigOrdinalType) {
        return new DPreType(BuiltInTypeDecl("ORDINAL"));
      } else if (type is BitvectorType bitvectorType) {
        return new DPreType(BuiltInTypeDecl("bv" + bitvectorType.Width));
      } else if (type is CollectionType) {
        var typeParameterCount = type is MapType ? 2 : 1;
        var name =
          type is SetType st ? (st.Finite ? "set" : "iset") :
          type is MultiSetType ? "multiset" :
          type is MapType mt ? (mt.Finite ? "map" : "imap") :
          "seq";
        var args = type.TypeArgs.ConvertAll(Type2PreType);
        return new DPreType(BuiltInTypeDecl(name, typeParameterCount), args);
      } else if (type is UserDefinedType udt) {
        var args = type.TypeArgs.ConvertAll(Type2PreType);
        return new DPreType(udt.ResolvedClass, args);
      } else if (type is TypeProxy) {
        return CreatePreTypeProxy();
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    public PreTypeResolver(Resolver resolver) {
      Contract.Requires(resolver != null);
      this.resolver = resolver;
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
    
    // ----------------------------------------

    void ClearState() {
      subtypeConstraints.Clear();
      comparableConstraints.Clear();
      guardedConstraints.Clear();
      defaultAdvice.Clear();
      confirmations.Clear();
    }
    
#if THIS_COMES_LATER
    public void PostResolveChecks(List<TopLevelDecl> declarations) {
      Contract.Requires(declarations != null);
      foreach (TopLevelDecl topd in declarations) {
        TopLevelDecl d = topd is ClassDecl ? ((ClassDecl)topd).NonNullTypeDecl : topd;
        if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          // this check can be done only after it has been determined that the redirected types do not involve cycles
          AddXConstraint(d.tok, "NumericType", dd.BaseType, "newtypes must be based on some numeric type (got {0})");
          if (dd.Var != null) {
            if (!CheckTypeInference_Visitor.IsDetermined(dd.BaseType.NormalizeExpand())) {
              ReportError(dd, "newtype's base type is not fully determined; add an explicit type for '{0}'", dd.Var.Name);
            }
          }
        } else if (d is SubsetTypeDecl) {
          var dd = (SubsetTypeDecl)d;
          if (!CheckTypeInference_Visitor.IsDetermined(dd.Rhs.NormalizeExpand())) {
            ReportError(dd, "subset type's base type is not fully determined; add an explicit type for '{0}'", dd.Var.Name);
          }
          dd.ConstraintIsCompilable = ExpressionTester.CheckIsCompilable(null, dd.Constraint, new CodeContextWrapper(dd, true));
          dd.CheckedIfConstraintIsCompilable = true;
          
          if (ErrorCount == prevErrCnt) {
            CheckTypeInference(dd.Witness, dd);
          }
          if (ErrorCount == prevErrCnt && dd.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
            ExpressionTester.CheckIsCompilable(this, dd.Witness, codeContext);
          }

        }
        
        Contract.Assert(AllTypeConstraints.Count == 0);
        if (ErrorCount == prevErrorCount) {
          // Check type inference, which also discovers bounds, in newtype/subset-type constraints and const declarations
          foreach (TopLevelDecl topd in declarations) {
            TopLevelDecl d = topd is ClassDecl ? ((ClassDecl)topd).NonNullTypeDecl : topd;
            if (d is RedirectingTypeDecl dd && dd.Constraint != null) {
              CheckTypeInference(dd.Constraint, dd);
            }
            if (topd is TopLevelDeclWithMembers cl) {
              foreach (var member in cl.Members) {
                if (member is ConstantField field && field.Rhs != null) {
                  // make sure initialization only refers to constant field or literal expression
                  if (CheckIsConstantExpr(field, field.Rhs)) {
                    AddAssignableConstraint(field.tok, field.Type, field.Rhs.Type,
                      "type for constant '" + field.Name + "' is '{0}', but its initialization value type is '{1}'");
                  }
                  
                  CheckTypeInference(field.Rhs, field);
                  if (!field.IsGhost) {
                    ExpressionTester.CheckIsCompilable(this, field.Rhs, field);
                  }
                }
              }
            }
          }
        }

      }
    }
#endif
    
    /// <summary>
    /// For every declaration in "declarations", resolve names and determine pre-types.
    /// </summary>
    public void ResolveDeclarations(List<TopLevelDecl> declarations) {
      Contract.Requires(declarations != null);
      
      foreach (TopLevelDecl d in declarations) {
        Contract.Assert(d != null);
        Contract.Assert(resolver.VisibleInScope(d));

        allTypeParameters.PushMarker();
        ResolveTypeParameters(d.TypeArgs, false, d);
        
        if (!(d is IteratorDecl)) {
          // Note, attributes of iterators are resolved by ResolvedIterator, after registering any names in the iterator signature
          ResolveAttributes(d.Attributes, d, new Resolver.ResolveOpts(new NoContext(d.EnclosingModuleDefinition), false), true);
        }

        if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          if (dd.Var == null) {
            Contract.Assert(dd.Constraint == null); // follows from NewtypeDecl invariant
          } else {
            Contract.Assert(object.ReferenceEquals(dd.Var.Type, dd.BaseType)); // follows from NewtypeDecl invariant
            Contract.Assert(dd.Constraint != null); // follows from NewtypeDecl invariant
            ResolveConstraintAndWitness(dd);
          }

        } else if (d is SubsetTypeDecl) {
          var dd = (SubsetTypeDecl)d;
          Contract.Assert(object.ReferenceEquals(dd.Var.Type, dd.Rhs)); // follows from SubsetTypeDecl invariant
          Contract.Assert(dd.Constraint != null); // follows from SubsetTypeDecl invariant

          ResolveConstraintAndWitness(dd);
          
        } else if (d is IteratorDecl iter) {
          // Note, attributes of iterators are resolved by ResolveIterator, after registering any names in the iterator signature.
          // The following method generates the iterator's members, which in turn are resolved below.
          ResolveIterator(iter);

        } else if (d is DatatypeDecl dt) {
          foreach (var ctor in dt.Ctors) {
            ResolveAttributes(ctor.Attributes, ctor, new Resolver.ResolveOpts(new NoContext(d.EnclosingModuleDefinition), false), true);
            foreach (var formal in ctor.Formals) {
#if TODO
              AddTypeDependencyEdges((ICallable)d, formal.Type);
#endif
            }
          }
          // resolve any default parameters
          foreach (var ctor in dt.Ctors) {
            scope.PushMarker();
            scope.AllowInstance = false;
            ctor.Formals.ForEach(p => scope.Push(p.Name, p));
            ResolveParameterDefaultValues(ctor.Formals, dt);
            scope.PopMarker();
          }
        }
        
        if (d is TopLevelDeclWithMembers dm) {
          currentClass = dm;
          foreach (var member in dm.Members) {
            Contract.Assert(resolver.VisibleInScope(member));
            ResolveMember(member);
          }
          currentClass = null;
        }
        
        allTypeParameters.PopMarker();
      }
    }
    
    void ResolveTypeParameters(List<TypeParameter> tparams, bool emitErrors, TypeParameter.ParentType parent) {
      Contract.Requires(tparams != null);
      Contract.Requires(parent != null);
      // push non-duplicated type parameter names
      int index = 0;
      foreach (TypeParameter tp in tparams) {
        if (emitErrors) {
          // we're seeing this TypeParameter for the first time
          tp.Parent = parent;
          tp.PositionalIndex = index;
        }
        var r = allTypeParameters.Push(tp.Name, tp);
        if (emitErrors) {
          if (r == Scope<TypeParameter>.PushResult.Duplicate) {
            ReportError(tp, "Duplicate type-parameter name: {0}", tp.Name);
          } else if (r == Scope<TypeParameter>.PushResult.Shadow) {
            ReportWarning(tp.tok, "Shadowed type-parameter name: {0}", tp.Name);
          }
        }
      }
    }
    
    void ResolveAttributes(Attributes attrs, IAttributeBearingDeclaration attributeHost, Resolver.ResolveOpts opts, bool solveConstraints) {
      Contract.Requires(opts != null);

      // order does not matter much for resolution, so resolve them in reverse order
      foreach (var attr in attrs.AsEnumerable()) {
        if (attributeHost != null && attr is UserSuppliedAttributes usa) {
#if TODO          
          usa.Recognized = resolver.IsRecognizedAttribute(usa, attributeHost); // TODO: this could be done in a later resolution pass
#endif
        }
        if (attr.Args != null) {
          attr.Args.Iter(arg => ResolveExpression(arg, opts));
          if (solveConstraints) {
            SolveAllTypeConstraints($"attribute of {attributeHost.ToString()}");
          }
        }
      }
    }

    void ResolveConstraintAndWitness(RedirectingTypeDecl dd) {
      Contract.Requires(dd != null);
      Contract.Requires(dd.Constraint != null);
      
      scope.PushMarker();
      var added = scope.Push(dd.Var.Name, dd.Var);
      Contract.Assert(added == Scope<IVariable>.PushResult.Success);

      ResolveExpression(dd.Constraint, new Resolver.ResolveOpts(new CodeContextWrapper(dd, true), false));
      ConstrainTypeExprBool(dd.Constraint, dd.WhatKind + " constraint must be of type bool (instead got {0})");
      SolveAllTypeConstraints($"{dd.WhatKind} '{dd.Name}' constraint");

      if (dd.Witness != null) {
        var prevErrCnt = ErrorCount;
        var codeContext = new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost);
        ResolveExpression(dd.Witness, new Resolver.ResolveOpts(codeContext, false));
        ConstrainSubtypeRelation(dd.Var.Type, dd.Witness.Type, dd.Witness, "witness expression must have type '{0}' (got '{1}')", dd.Var.Type,
          dd.Witness.Type);
        SolveAllTypeConstraints($"{dd.WhatKind} '{dd.Name}' witness");
      }
      
      scope.PopMarker();
    }

    void ResolveParameterDefaultValues(List<Formal> formals, ICodeContext codeContext) {
      Contract.Requires(formals != null);
      Contract.Requires(codeContext != null);

      var dependencies = new Graph<IVariable>();
      var allowMoreRequiredParameters = true;
      var allowNamelessParameters = true;
      foreach (var formal in formals) {
        var d = formal.DefaultValue;
        if (d != null) {
          allowMoreRequiredParameters = false;
          ResolveExpression(d, new Resolver.ResolveOpts(codeContext, codeContext is TwoStateFunction || codeContext is TwoStateLemma));
          AddAssignableConstraint(d.tok, formal.Type, d.Type, "default-value expression (of type '{1}') is not assignable to formal (of type '{0}')");
          foreach (var v in Resolver.FreeVariables(d)) {
            dependencies.AddEdge(formal, v);
          }
        } else if (!allowMoreRequiredParameters) {
          ReportError(formal.tok, "a required parameter must precede all optional parameters");
        }
        if (!allowNamelessParameters && !formal.HasName) {
          ReportError(formal.tok, "a nameless parameter must precede all nameonly parameters");
        }
        if (formal.IsNameOnly) {
          allowNamelessParameters = false;
        }
      }
      SolveAllTypeConstraints($"parameter default values of {codeContext.FullSanitizedName}");

      foreach (var cycle in dependencies.AllCycles()) {
        var cy = Util.Comma(" -> ", cycle, v => v.Name) + " -> " + cycle[0].Name;
        ReportError(cycle[0].Tok, $"default-value expressions for parameters contain a cycle: {cy}");
      }
    }

    void ResolveMember(MemberDecl member) {
      Contract.Requires(member != null);
      Contract.Requires(currentClass != null);
      
      if (member is ConstantField cfield) {
        var opts = new Resolver.ResolveOpts(cfield, false);
        ResolveAttributes(member.Attributes, cfield, opts, true);
        if (cfield.Rhs != null) {
          ResolveExpression(cfield.Rhs, opts);
        }
        
      } else if (member is Field) {
        var opts = new Resolver.ResolveOpts(new NoContext(currentClass.EnclosingModuleDefinition), false);
        ResolveAttributes(member.Attributes, member, opts, true);
        
      } else if (member is Function f) {
        var ec = ErrorCount;
        allTypeParameters.PushMarker();
        ResolveTypeParameters(f.TypeArgs, false, f);
        ResolveFunction(f);
        allTypeParameters.PopMarker();
        
        if (f is ExtremePredicate ef && ef.PrefixPredicate != null && ec == ErrorCount) {
          var ff = ef.PrefixPredicate;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(ff.TypeArgs, false, ff);
          ResolveFunction(ff);
          allTypeParameters.PopMarker();
        }

      } else if (member is Method m) {
        var ec = ErrorCount;
        allTypeParameters.PushMarker();
        ResolveTypeParameters(m.TypeArgs, false, m);
        ResolveMethod(m);
        allTypeParameters.PopMarker();
        
        if (m is ExtremeLemma em && em.PrefixLemma != null && ec == ErrorCount) {
          var mm = em.PrefixLemma;
          allTypeParameters.PushMarker();
          ResolveTypeParameters(mm.TypeArgs, false, mm);
          ResolveMethod(mm);
          allTypeParameters.PopMarker();
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
      }
    }
    
    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveIterator(IteratorDecl iter) {
      Contract.Requires(iter != null);
      Contract.Requires(currentClass != null);
      Contract.Ensures(currentClass == null);

      var initialErrorCount = ErrorCount;

      // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
      scope.PushMarker();
      scope.AllowInstance = false;  // disallow 'this' from use, which means that the special fields and methods added are not accessible in the syntactically given spec
      iter.Ins.ForEach(p => scope.Push(p.Name, p));
      ResolveParameterDefaultValues(iter.Ins, iter);

      // Start resolving specification...
      // we start with the decreases clause, because the _decreases<n> fields were only given type proxies before; we'll know
      // the types only after resolving the decreases clause (and it may be that some of resolution has already seen uses of
      // these fields; so, with no further ado, here we go
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (int i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var e = iter.Decreases.Expressions[i];
        ResolveExpression(e, new Resolver.ResolveOpts(iter, false));
        // any type is fine, but associate this type with the corresponding _decreases<n> field
        var d = iter.DecreasesFields[i];
        // If the following type constraint does not hold, then: Bummer, there was a use--and a bad use--of the field before, so this won't be the best of error messages
        ConstrainSubtypeRelation(d.Type, e.Type, e, "type of field {0} is {1}, but has been constrained elsewhere to be of type {2}", d.Name, e.Type, d.Type);
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        ResolveFrameExpression(fe, Resolver.FrameExpressionUse.Reads, iter);
      }
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        ResolveFrameExpression(fe, Resolver.FrameExpressionUse.Modifies, iter);
      }
      foreach (AttributedExpression e in iter.Requires) {
        ResolveExpression(e.E, new Resolver.ResolveOpts(iter, false));
        ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
      }

      scope.PopMarker();  // for the in-parameters

      // We resolve the rest of the specification in an instance context.  So mentions of the in- or yield-parameters
      // get resolved as field dereferences (with an implicit "this")
      scope.PushMarker();
      currentClass = iter;
      Contract.Assert(scope.AllowInstance);

      foreach (AttributedExpression e in iter.YieldRequires) {
        ResolveExpression(e.E, new Resolver.ResolveOpts(iter, false));
        ConstrainTypeExprBool(e.E, "Yield precondition must be a boolean (got {0})");
      }
      foreach (AttributedExpression e in iter.YieldEnsures) {
        ResolveExpression(e.E, new Resolver.ResolveOpts(iter, true));
        ConstrainTypeExprBool(e.E, "Yield postcondition must be a boolean (got {0})");
      }
      foreach (AttributedExpression e in iter.Ensures) {
        ResolveExpression(e.E, new Resolver.ResolveOpts(iter, true));
        ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
      }
      SolveAllTypeConstraints($"specification of iterator '{iter.Name}'");

      ResolveAttributes(iter.Attributes, iter, new Resolver.ResolveOpts(iter, false), true);

      var postSpecErrorCount = ErrorCount;

      // Resolve body
      if (iter.Body != null) {
        dominatingStatementLabels.PushMarker();
        foreach (var req in iter.Requires) {
          if (req.Label != null) {
            if (dominatingStatementLabels.Find(req.Label.Name) != null) {
              ReportError(req.Label.Tok, "assert label shadows a dominating label");
            } else {
              var rr = dominatingStatementLabels.Push(req.Label.Name, req.Label);
              Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
            }
          }
        }
        ResolveBlockStatement(iter.Body, iter);
        dominatingStatementLabels.PopMarker();
        SolveAllTypeConstraints($"body of iterator '{iter.Name}'");
      }

      currentClass = null;
      scope.PopMarker();  // pop off the AllowInstance setting

      if (postSpecErrorCount == initialErrorCount) {
        resolver.CreateIteratorMethodSpecs(iter);
      }
    }
    
    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveFunction(Function f) {
      Contract.Requires(f != null);

      bool warnShadowingOption = DafnyOptions.O.WarnShadowing;  // save the original warnShadowing value
      bool warnShadowing = false;

      scope.PushMarker();
      if (f.IsStatic) {
        scope.AllowInstance = false;
      }

      if (f.IsGhost) {
        // TODO: the following could be done in a different resolver pass
        foreach (TypeParameter p in f.TypeArgs) {
          if (p.SupportsEquality) {
            ReportWarning(p.tok,
              $"type parameter {p.Name} of ghost {f.WhatKind} {f.Name} is declared (==), which is unnecessary because the {f.WhatKind} doesn't contain any compiled code");
          }
        }
      }

      foreach (Formal p in f.Formals) {
        scope.Push(p.Name, p);
      }
      ResolveAttributes(f.Attributes, f, new Resolver.ResolveOpts(f, false), true);
      // take care of the warnShadowing attribute
      if (Attributes.ContainsBool(f.Attributes, "warnShadowing", ref warnShadowing)) {
        DafnyOptions.O.WarnShadowing = warnShadowing;  // set the value according to the attribute
      }
      ResolveParameterDefaultValues(f.Formals, f);
      foreach (AttributedExpression e in f.Req) {
        ResolveAttributes(e.Attributes, e, new Resolver.ResolveOpts(f, f is TwoStateFunction), false);
        Expression r = e.E;
        ResolveExpression(r, new Resolver.ResolveOpts(f, f is TwoStateFunction));
        ConstrainTypeExprBool(r, "Precondition must be a boolean (got {0})");
      }
      foreach (FrameExpression fr in f.Reads) {
        ResolveFrameExpression(fr, Resolver.FrameExpressionUse.Reads, f);
      }
      foreach (AttributedExpression e in f.Ens) {
        Expression r = e.E;
        if (f.Result != null) {
          scope.PushMarker();
          scope.Push(f.Result.Name, f.Result);  // function return only visible in post-conditions
        }
        ResolveExpression(r, new Resolver.ResolveOpts(f, f is TwoStateFunction, false, true, false));  // since this is a function, the postcondition is still a one-state predicate, unless it's a two-state function
        ConstrainTypeExprBool(r, "Postcondition must be a boolean (got {0})");
        if (f.Result != null) {
          scope.PopMarker();
        }
      }
      ResolveAttributes(f.Decreases.Attributes, f.Decreases, new Resolver.ResolveOpts(f, f is TwoStateFunction), false);
      foreach (Expression r in f.Decreases.Expressions) {
        ResolveExpression(r, new Resolver.ResolveOpts(f, f is TwoStateFunction));
        // any type is fine
      }
      SolveAllTypeConstraints($"specification of {f.WhatKind} '{f.Name}'");

      if (f.ByMethodBody != null) {
        // The following conditions are assured by the parser and other callers of the Function constructor
        Contract.Assert(f.Body != null);
        Contract.Assert(!f.IsGhost);
      }
      if (f.Body != null) {
        var prevErrorCount = ErrorCount;
        ResolveExpression(f.Body, new Resolver.ResolveOpts(f, f is TwoStateFunction));
        AddAssignableConstraint(f.tok, f.ResultType, f.Body.Type, "Function body type mismatch (expected {0}, got {1})");
        SolveAllTypeConstraints($"body of {f.WhatKind} '{f.Name}'");

        if (f.ByMethodBody != null) {
          var method = f.ByMethodDecl;
          Contract.Assert(method != null); // this should have been filled in by now
          ResolveMethod(method);
        }
      }

      scope.PopMarker();

      DafnyOptions.O.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
    }
    
    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveMethod(Method m) {
      Contract.Requires(m != null);

      try {
        currentMethod = m;

        bool warnShadowingOption = DafnyOptions.O.WarnShadowing;  // save the original warnShadowing value
        bool warnShadowing = false;
        // take care of the warnShadowing attribute
        if (Attributes.ContainsBool(m.Attributes, "warnShadowing", ref warnShadowing)) {
          DafnyOptions.O.WarnShadowing = warnShadowing;  // set the value according to the attribute
        }

        if (m.IsGhost) {
          foreach (TypeParameter p in m.TypeArgs) {
            if (p.SupportsEquality) {
              ReportWarning(p.tok,
                $"type parameter {p.Name} of ghost {m.WhatKind} {m.Name} is declared (==), which is unnecessary because the {m.WhatKind} doesn't contain any compiled code");
            }
          }
        }

        // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
        scope.PushMarker();
        if (m.IsStatic || m is Constructor) {
          scope.AllowInstance = false;
        }
        foreach (Formal p in m.Ins) {
          scope.Push(p.Name, p);
        }
        ResolveParameterDefaultValues(m.Ins, m);

        // Start resolving specification...
        foreach (AttributedExpression e in m.Req) {
          ResolveAttributes(e.Attributes, e, new Resolver.ResolveOpts(m, m is TwoStateLemma), false);
          ResolveExpression(e.E, new Resolver.ResolveOpts(m, m is TwoStateLemma));
          ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
        }

        ResolveAttributes(m.Mod.Attributes, m.Mod, new Resolver.ResolveOpts(m, false), false);
        foreach (FrameExpression fe in m.Mod.Expressions) {
          ResolveFrameExpression(fe, Resolver.FrameExpressionUse.Modifies, m);
          if (m.IsLemmaLike) {
            ReportError(fe.tok, "{0}s are not allowed to have modifies clauses", m.WhatKind);
          } else if (m.IsGhost) {
#if TODO
            DisallowNonGhostFieldSpecifiers(fe);
#endif
          }
        }
        ResolveAttributes(m.Decreases.Attributes, m.Decreases, new Resolver.ResolveOpts(m, false), false);
        foreach (Expression e in m.Decreases.Expressions) {
          ResolveExpression(e, new Resolver.ResolveOpts(m, m is TwoStateLemma));
          // any type is fine
        }

        if (m is Constructor) {
          scope.PopMarker();
          // start the scope again, but this time allowing instance
          scope.PushMarker();
          foreach (Formal p in m.Ins) {
            scope.Push(p.Name, p);
          }
        }

        // Add out-parameters to a new scope that will also include the outermost-level locals of the body
        // Don't care about any duplication errors among the out-parameters, since they have already been reported
        scope.PushMarker();
        if (m is ExtremeLemma && m.Outs.Count != 0) {
          ReportError(m.Outs[0].tok, "{0}s are not allowed to have out-parameters", m.WhatKind);
        } else {
          foreach (Formal p in m.Outs) {
            scope.Push(p.Name, p);
          }
        }

        // ... continue resolving specification
        foreach (AttributedExpression e in m.Ens) {
          ResolveAttributes(e.Attributes, e, new Resolver.ResolveOpts(m, true), false);
          ResolveExpression(e.E, new Resolver.ResolveOpts(m, true));
          ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
        }
        SolveAllTypeConstraints($"specification of {m.WhatKind} '{m.Name}'");

        // Resolve body
        if (m.Body != null) {
          var com = m as ExtremeLemma;
          if (com != null && com.PrefixLemma != null) {
            // The body may mentioned the implicitly declared parameter _k.  Throw it into the
            // scope before resolving the body.
            var k = com.PrefixLemma.Ins[0];
            scope.Push(k.Name, k);  // we expect no name conflict for _k
          }

          dominatingStatementLabels.PushMarker();
          foreach (var req in m.Req) {
            if (req.Label != null) {
              if (dominatingStatementLabels.Find(req.Label.Name) != null) {
                ReportError(req.Label.Tok, "assert label shadows a dominating label");
              } else {
                var rr = dominatingStatementLabels.Push(req.Label.Name, req.Label);
                Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
              }
            }
          }
          ResolveBlockStatement(m.Body, m);
          dominatingStatementLabels.PopMarker();
          SolveAllTypeConstraints($"body of {m.WhatKind} '{m.Name}'");
        }

        // attributes are allowed to mention both in- and out-parameters (including the implicit _k, for greatest lemmas)
        ResolveAttributes(m.Attributes, m, new Resolver.ResolveOpts(m, m is TwoStateLemma), true);

        DafnyOptions.O.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
        scope.PopMarker();  // for the out-parameters and outermost-level locals
        scope.PopMarker();  // for the in-parameters
      }
      finally {
        currentMethod = null;
      }
    }

    void ResolveFrameExpression(FrameExpression fe, Resolver.FrameExpressionUse use, ICodeContext codeContext) {
      Contract.Requires(fe != null);
      Contract.Requires(codeContext != null);
      ResolveExpression(fe.E, new Resolver.ResolveOpts(codeContext, codeContext is TwoStateLemma || use == Resolver.FrameExpressionUse.Unchanged));
      var eventualRefType = new InferredTypeProxy();
#if TODO
      Type t = fe.E.Type;
      if (use == Resolver.FrameExpressionUse.Reads) {
        AddXConstraint(fe.E.tok, "ReadsFrame", t, eventualRefType,
          "a reads-clause expression must denote an object, a set/iset/multiset/seq of objects, or a function to a set/iset/multiset/seq of objects (instead got {0})");
      } else {
        AddXConstraint(fe.E.tok, "ModifiesFrame", t, eventualRefType,
          use == Resolver.FrameExpressionUse.Modifies ?
          "a modifies-clause expression must denote an object or a set/iset/multiset/seq of objects (instead got {0})" :
          "an unchanged expression must denote an object or a set/iset/multiset/seq of objects (instead got {0})");
      }
#endif
      if (fe.FieldName != null) {
        NonProxyType tentativeReceiverType;
        var member = FindMember(fe.E.tok, eventualRefType, fe.FieldName, out tentativeReceiverType);
        var ctype = (UserDefinedType)tentativeReceiverType;  // correctness of cast follows from the DenotesClass test above
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (!(member is Field)) {
          ReportError(fe.E, "member {0} in type {1} does not refer to a field", fe.FieldName, ctype.Name);
        } else if (member is ConstantField) {
          ReportError(fe.E, "expression is not allowed to refer to constant field {0}", fe.FieldName);
        } else {
          Contract.Assert(ctype != null && ctype.ResolvedClass != null);  // follows from postcondition of ResolveMember
          fe.Field = (Field)member;
        }
      }
    }

    void ResolveBlockStatement(BlockStmt blockStmt, ICodeContext codeContext) {
      // TODO
    }

    void ResolveExpression(Expression expr, Resolver.ResolveOpts opts) {
      Contract.Requires(expr != null);
      Contract.Requires(opts != null);
      
      if (expr.PreType != null) {
        // expression has already been pre-resolved
        return;
      }
      
      if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        ResolveExpression(e.E, opts);
        e.ResolvedExpression = e.E;
        e.PreType = e.E.PreType;

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        ResolveExpression(e.E, opts);
        e.ResolvedExpression = e.E;
        e.PreType = e.E.PreType;

#if SOON
      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        ResolveExpression(e.E, opts);
        e.Type = e.E.Type;
        AddXConstraint(e.E.tok, "NumericOrBitvector", e.E.Type, "type of unary - must be of a numeric or bitvector type (instead got {0})");
        // Note, e.ResolvedExpression will be filled in during CheckTypeInference, at which time e.Type has been determined
#endif
      } else if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;

        if (e is StaticReceiverExpr eStatic) {
          resolver.ResolveType(eStatic.tok, eStatic.UnresolvedType, opts.codeContext, Resolver.ResolveTypeOptionEnum.InferTypeProxies, null);
          eStatic.PreType = Type2PreType(eStatic.UnresolvedType);
        } else {
          if (e.Value == null) {
            e.PreType = CreatePreTypeProxy();
            AddConfirmation(e.tok, "IsNullableRefType", e.PreType, "type of 'null' is a reference type, but it is used as {0}");
          } else if (e.Value is BigInteger) {
            e.PreType = CreatePreTypeProxy();
            AddDefaultAdvice(e.PreType, AdviceTarget.Int);
            AddConfirmation(e.tok, "InIntFamily", e.PreType, "integer literal used as if it had type {0}");
          } else if (e.Value is BaseTypes.BigDec) {
            e.PreType = CreatePreTypeProxy();
            AddDefaultAdvice(e.PreType, AdviceTarget.Real);
            AddConfirmation(e.tok, "InRealFamily", e.PreType, "type of real literal is used as {0}"); // TODO: make this error message have the same form as the one for integers above
          } else if (e.Value is bool) {
            e.PreType = CreatePreTypeProxy();
            AddDefaultAdvice(e.PreType, AdviceTarget.Bool);
            AddConfirmation(e.tok, "InBoolFamily", e.PreType, "boolean literal used as if it had type {0}");
          } else if (e is CharLiteralExpr) {
            e.PreType = CreatePreTypeProxy();
            AddDefaultAdvice(e.PreType, AdviceTarget.Char);
            AddConfirmation(e.tok, "InCharFamily", e.PreType, "character literal used as if it had type {0}");
          } else if (e is StringLiteralExpr) {
            e.PreType = CreatePreTypeProxy();
            AddDefaultAdvice(e.PreType, AdviceTarget.String);
            AddConfirmation(e.tok, "InSeqFamily", e.PreType, "string literal used as if it had type {0}");
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal type
          }
        }

      } else if (expr is ThisExpr) {
        if (!scope.AllowInstance) {
          ReportError(expr, "'this' is not allowed in a 'static' context");
        }
        if (currentClass is ClassDecl cd && cd.IsDefaultClass) {
          // there's no type
        } else {
          var ty = Resolver.GetThisType(expr.tok, currentClass);  // do this regardless of scope.AllowInstance, for better error reporting 
          expr.PreType = Type2PreType(ty);
        }

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        e.Var = scope.Find(e.Name);
        if (e.Var != null) {
          expr.PreType = Type2PreType(e.Var.Type);
        } else {
          ReportError(expr, "Identifier does not denote a local variable, parameter, or bound variable: {0}", e.Name);
        }
#if SOON
      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        TopLevelDecl d;
        if (!moduleInfo.TopLevels.TryGetValue(dtv.DatatypeName, out d)) {
          ReportError(expr.tok, "Undeclared datatype: {0}", dtv.DatatypeName);
        } else if (d is AmbiguousTopLevelDecl) {
          var ad = (AmbiguousTopLevelDecl)d;
          ReportError(expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", dtv.DatatypeName, ad.ModuleNames());
        } else if (!(d is DatatypeDecl)) {
          ReportError(expr.tok, "Expected datatype: {0}", dtv.DatatypeName);
        } else {
          ResolveDatatypeValue(opts, dtv, (DatatypeDecl)d, null);
        }

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        Type elementType = new InferredTypeProxy() { KeepConstraints = true };
        foreach (Expression ee in e.Elements) {
          ResolveExpression(ee, opts);
          ConstrainSubtypeRelation(elementType, ee.Type, ee.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", ee.Type, elementType);
        }
        if (expr is SetDisplayExpr) {
          var se = (SetDisplayExpr)expr;
          expr.Type = new SetType(se.Finite, elementType);
        } else if (expr is MultiSetDisplayExpr) {
          expr.Type = new MultiSetType(elementType);
        } else {
          expr.Type = new SeqType(elementType);
        }
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        Type domainType = new InferredTypeProxy();
        Type rangeType = new InferredTypeProxy();
        foreach (ExpressionPair p in e.Elements) {
          ResolveExpression(p.A, opts);
          ConstrainSubtypeRelation(domainType, p.A.Type, p.A.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", p.A.Type, domainType);
          ResolveExpression(p.B, opts);
          ConstrainSubtypeRelation(rangeType, p.B.Type, p.B.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", p.B.Type, rangeType);
        }
        expr.Type = new MapType(e.Finite, domainType, rangeType);
#endif
      } else if (expr is NameSegment) {
        var e = (NameSegment)expr;
        ResolveNameSegment(e, true, null, opts, false);

        if (e.Type is Resolver_IdentifierExpr.ResolverType_Module) {
          ReportError(e.tok, "name of module ({0}) is used as a variable", e.Name);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        } else if (e.Type is Resolver_IdentifierExpr.ResolverType_Type) {
          ReportError(e.tok, "name of type ({0}) is used as a variable", e.Name);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        }

#if TODO
      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        ResolveDotSuffix(e, true, null, opts, false);
        if (e.Type is Resolver_IdentifierExpr.ResolverType_Module) {
          ReportError(e.tok, "name of module ({0}) is used as a variable", e.SuffixName);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        } else if (e.Type is Resolver_IdentifierExpr.ResolverType_Type) {
          ReportError(e.tok, "name of type ({0}) is used as a variable", e.SuffixName);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        }

      } else if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        ResolveApplySuffix(e, opts, false);

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        ResolveExpression(e.Obj, opts);
        NonProxyType tentativeReceiverType;
        var member = ResolveMember(expr.tok, e.Obj.Type, e.MemberName, out tentativeReceiverType);
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (member is Function) {
          var fn = member as Function;
          e.Member = fn;
          if (fn is TwoStateFunction && !opts.twoState) {
            ReportError(e.tok, "a two-state function can be used only in a two-state context");
          }
          // build the type substitution map
          e.TypeApplication_AtEnclosingClass = tentativeReceiverType.TypeArgs;
          e.TypeApplication_JustMember = new List<Type>();
          Dictionary<TypeParameter, Type> subst;
          var ctype = tentativeReceiverType as UserDefinedType;
          if (ctype == null) {
            subst = new Dictionary<TypeParameter, Type>();
          } else {
            subst = TypeSubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
          }
          foreach (var tp in fn.TypeArgs) {
            Type prox = new InferredTypeProxy();
            subst[tp] = prox;
            e.TypeApplication_JustMember.Add(prox);
          }
          subst = BuildTypeArgumentSubstitute(subst);
          e.Type = SelectAppropriateArrowType(fn.tok, fn.Formals.ConvertAll(f => SubstType(f.Type, subst)), SubstType(fn.ResultType, subst),
            fn.Reads.Count != 0, fn.Req.Count != 0);
          AddCallGraphEdge(opts.codeContext, fn, e, false);
        } else if (member is Field) {
          var field = (Field)member;
          e.Member = field;
          e.TypeApplication_AtEnclosingClass = tentativeReceiverType.TypeArgs;
          e.TypeApplication_JustMember = new List<Type>();
          if (e.Obj is StaticReceiverExpr && !field.IsStatic) {
            ReportError(expr, "a field must be selected via an object, not just a class name");
          }
          var ctype = tentativeReceiverType as UserDefinedType;
          if (ctype == null) {
            e.Type = field.Type;
          } else {
            Contract.Assert(ctype.ResolvedClass != null); // follows from postcondition of ResolveMember
            // build the type substitution map
            var subst = TypeSubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
            e.Type = SubstType(field.Type, subst);
          }
          AddCallGraphEdgeForField(opts.codeContext, field, e);
        } else {
          ReportError(expr, "member {0} in type {1} does not refer to a field or a function", e.MemberName, tentativeReceiverType);
        }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        ResolveSeqSelectExpr(e, opts);

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;

        ResolveExpression(e.Array, opts);
        Contract.Assert(e.Array.Type.TypeArgs != null);  // if it is null, should make a 1-element list with a Proxy
        Type elementType = e.Array.Type.TypeArgs.Count > 0 ?
          e.Array.Type.TypeArgs[0] :
          new InferredTypeProxy();
        ConstrainSubtypeRelation(ResolvedArrayType(e.Array.tok, e.Indices.Count, elementType, opts.codeContext, true), e.Array.Type, e.Array,
          "array selection requires an array{0} (got {1})", e.Indices.Count, e.Array.Type);
        int i = 0;
        foreach (Expression idx in e.Indices) {
          Contract.Assert(idx != null);
          ResolveExpression(idx, opts);
          ConstrainToIntegerType(idx, true, "array selection requires integer- or bitvector-based numeric indices (got {0} for index " + i + ")");
          i++;
        }
        e.Type = elementType;

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        ResolveExpression(e.Seq, opts);
        ResolveExpression(e.Index, opts);
        ResolveExpression(e.Value, opts);
        AddXConstraint(expr.tok, "SeqUpdatable", e.Seq.Type, e.Index, e.Value, "update requires a sequence, map, or multiset (got {0})");
        expr.Type = e.Seq.Type;

      } else if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        ResolveExpression(e.Root, opts);
        var ty = PartiallyResolveTypeForMemberSelection(expr.tok, e.Root.Type);
        if (!ty.IsDatatype) {
          ReportError(expr, "datatype update expression requires a root expression of a datatype (got {0})", ty);
        } else {
          List<DatatypeCtor> legalSourceConstructors;
          var let = ResolveDatatypeUpdate(expr.tok, e.Root, ty.AsDatatype, e.Updates, opts, out legalSourceConstructors);
          if (let != null) {
            e.ResolvedExpression = let;
            e.LegalSourceConstructors = legalSourceConstructors;
            expr.Type = ty;
          }
        }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        ResolveFunctionCallExpr(e, opts);

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        ResolveExpression(e.Function, opts);
        foreach (var arg in e.Args) {
          ResolveExpression(arg, opts);
        }

        // TODO: the following should be replaced by a type-class constraint that constrains the types of e.Function, e.Args[*], and e.Type
        var fnType = e.Function.Type.AsArrowType;
        if (fnType == null) {
          ReportError(e.tok,
            "non-function expression (of type {0}) is called with parameters", e.Function.Type);
        } else if (fnType.Arity != e.Args.Count) {
          ReportError(e.tok,
            "wrong number of arguments to function application (function type '{0}' expects {1}, got {2})", fnType,
            fnType.Arity, e.Args.Count);
        } else {
          for (var i = 0; i < fnType.Arity; i++) {
            AddAssignableConstraint(e.Args[i].tok, fnType.Args[i], e.Args[i].Type,
              "type mismatch for argument" + (fnType.Arity == 1 ? "" : " " + i) + " (function expects {0}, got {1})");
          }
        }

        expr.Type = fnType == null ? new InferredTypeProxy() : fnType.Result;

      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        var elementType = e.ExplicitElementType ?? new InferredTypeProxy();
        ResolveType(e.tok, elementType, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        ResolveExpression(e.N, opts);
        ConstrainToIntegerType(e.N, false, "sequence construction must use an integer-based expression for the sequence size (got {0})");
        ResolveExpression(e.Initializer, opts);
        var arrowType = new ArrowType(e.tok, builtIns.ArrowTypeDecls[1], new List<Type>() { builtIns.Nat() }, elementType);
        var hintString = " (perhaps write '_ =>' in front of the expression you gave in order to make it an arrow type)";
        ConstrainSubtypeRelation(arrowType, e.Initializer.Type, e.Initializer, "sequence-construction initializer expression expected to have type '{0}' (instead got '{1}'){2}",
          arrowType, e.Initializer.Type, new LazyString_OnTypeEquals(elementType, e.Initializer.Type, hintString));
        expr.Type = new SeqType(elementType);

      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        ResolveExpression(e.E, opts);
        var elementType = new InferredTypeProxy();
        AddXConstraint(e.E.tok, "MultiSetConvertible", e.E.Type, elementType, "can only form a multiset from a seq or set (got {0})");
        expr.Type = new MultiSetType(elementType);

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        e.AtLabel = ResolveDominatingLabelInExpr(expr.tok, e.At, "old", opts);
        ResolveExpression(e.E, new ResolveOpts(opts.codeContext, false, opts.isReveal, opts.isPostCondition, true));
        expr.Type = e.E.Type;

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        e.AtLabel = ResolveDominatingLabelInExpr(expr.tok, e.At, "unchanged", opts);
        foreach (var fe in e.Frame) {
          ResolveFrameExpression(fe, FrameExpressionUse.Unchanged, opts.codeContext);
        }
        expr.Type = Type.Bool;

      } else if (expr is FreshExpr) {
        var e = (FreshExpr)expr;
        ResolveExpression(e.E, opts);
        e.AtLabel = ResolveDominatingLabelInExpr(expr.tok, e.At, "fresh", opts);
        // the type of e.E must be either an object or a set/seq of objects
        AddXConstraint(expr.tok, "Freshable", e.E.Type, "the argument of a fresh expression must denote an object or a set or sequence of objects (instead got {0})");
        expr.Type = Type.Bool;

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        ResolveExpression(e.E, opts);
        switch (e.Op) {
          case UnaryOpExpr.Opcode.Not:
            AddXConstraint(e.E.tok, "BooleanBits", e.E.Type, "logical/bitwise negation expects a boolean or bitvector argument (instead got {0})");
            expr.Type = e.E.Type;
            break;
          case UnaryOpExpr.Opcode.Cardinality:
            AddXConstraint(expr.tok, "Sizeable", e.E.Type, "size operator expects a collection argument (instead got {0})");
            expr.Type = Type.Int;
            break;
          case UnaryOpExpr.Opcode.Allocated:
            // the argument is allowed to have any type at all
            expr.Type = Type.Bool;
            if (2 <= DafnyOptions.O.Allocated &&
              ((opts.codeContext is Function && !opts.InsideOld) || opts.codeContext is ConstantField || CodeContextWrapper.Unwrap(opts.codeContext) is RedirectingTypeDecl)) {
              var declKind = CodeContextWrapper.Unwrap(opts.codeContext) is RedirectingTypeDecl redir ? redir.WhatKind : ((MemberDecl)opts.codeContext).WhatKind;
              ReportError(expr, "a {0} definition is not allowed to depend on the set of allocated references", declKind);
            }
            break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary operator
        }

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        ResolveExpression(e.E, opts);
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveType(e.tok, e.ToType, opts.codeContext, new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null);
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          if (e.ToType.IsNumericBased(Type.NumericPersuasion.Int)) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to an int-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to a real-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsBitVectorType) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to a bitvector-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsCharType) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to a char type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsBigOrdinalType) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to an ORDINAL type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsRefType) {
            AddAssignableConstraint(expr.tok, e.ToType, e.E.Type, "type cast to reference type '{0}' must be from an expression assignable to it (got '{1}')");
          } else {
            ReportError(expr, "type conversions are not supported to this type (got {0})", e.ToType);
          }
          e.Type = e.ToType;
        } else {
          e.Type = new InferredTypeProxy();
        }

      } else if (expr is TypeTestExpr) {
        var e = (TypeTestExpr)expr;
        ResolveExpression(e.E, opts);
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveType(e.tok, e.ToType, opts.codeContext, new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null);
        AddAssignableConstraint(expr.tok, e.ToType, e.E.Type, "type test for type '{0}' must be from an expression assignable to it (got '{1}')");
        e.Type = Type.Bool;
#endif

      } else if (expr is BinaryExpr) {

        BinaryExpr e = (BinaryExpr)expr;
        ResolveExpression(e.E0, opts);
        ResolveExpression(e.E1, opts);

        switch (e.Op) {
#if SOON
          case BinaryExpr.Opcode.Iff:
          case BinaryExpr.Opcode.Imp:
          case BinaryExpr.Opcode.Exp:
          case BinaryExpr.Opcode.And:
          case BinaryExpr.Opcode.Or: {
              ConstrainSubtypeRelation(Type.Bool, e.E0.Type, expr, "first argument to {0} must be of type bool (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
              ConstrainSubtypeRelation(Type.Bool, e.E1.Type, expr, "second argument to {0} must be of type bool (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E1.Type);
              expr.Type = Type.Bool;
              break;
            }

          case BinaryExpr.Opcode.Eq:
          case BinaryExpr.Opcode.Neq:
            AddXConstraint(expr.tok, "Equatable", e.E0.Type, e.E1.Type, "arguments must have comparable types (got {0} and {1})");
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Disjoint:
            Type disjointArgumentsType = new InferredTypeProxy();
            ConstrainSubtypeRelation(disjointArgumentsType, e.E0.Type, expr, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
            ConstrainSubtypeRelation(disjointArgumentsType, e.E1.Type, expr, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
            AddXConstraint(expr.tok, "Disjointable", disjointArgumentsType, "arguments must be of a set or multiset type (got {0})");
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Lt:
          case BinaryExpr.Opcode.Le: {
              if (e.Op == BinaryExpr.Opcode.Lt && (PartiallyResolveTypeForMemberSelection(e.E0.tok, e.E0.Type).IsIndDatatype || e.E0.Type.IsTypeParameter || PartiallyResolveTypeForMemberSelection(e.E1.tok, e.E1.Type).IsIndDatatype)) {
                AddXConstraint(expr.tok, "RankOrderable", e.E0.Type, e.E1.Type, "arguments to rank comparison must be datatypes (got {0} and {1})");
                e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankLt;
              } else {
                var cmpType = new InferredTypeProxy();
                var err = new TypeConstraint.ErrorMsgWithToken(expr.tok, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
                ConstrainSubtypeRelation(cmpType, e.E0.Type, err);
                ConstrainSubtypeRelation(cmpType, e.E1.Type, err);
                AddXConstraint(expr.tok, "Orderable_Lt", e.E0.Type, e.E1.Type,
                  "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be of a numeric type, bitvector type, ORDINAL, char, a sequence type, or a set-like type (instead got {0} and {1})");
              }
              expr.Type = Type.Bool;
            }
            break;

          case BinaryExpr.Opcode.Gt:
          case BinaryExpr.Opcode.Ge: {
              if (e.Op == BinaryExpr.Opcode.Gt && (PartiallyResolveTypeForMemberSelection(e.E0.tok, e.E0.Type).IsIndDatatype || PartiallyResolveTypeForMemberSelection(e.E1.tok, e.E1.Type).IsIndDatatype || e.E1.Type.IsTypeParameter)) {
                AddXConstraint(expr.tok, "RankOrderable", e.E1.Type, e.E0.Type, "arguments to rank comparison must be datatypes (got {1} and {0})");
                e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankGt;
              } else {
                var cmpType = new InferredTypeProxy();
                var err = new TypeConstraint.ErrorMsgWithToken(expr.tok, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
                ConstrainSubtypeRelation(cmpType, e.E0.Type, err);
                ConstrainSubtypeRelation(cmpType, e.E1.Type, err);
                AddXConstraint(expr.tok, "Orderable_Gt", e.E0.Type, e.E1.Type,
                  "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be of a numeric type, bitvector type, ORDINAL, char, or a set-like type (instead got {0} and {1})");
              }
              expr.Type = Type.Bool;
            }
            break;

          case BinaryExpr.Opcode.LeftShift:
          case BinaryExpr.Opcode.RightShift: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "IsBitvector", expr.Type, "type of " + BinaryExpr.OpcodeString(e.Op) + " must be a bitvector type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              AddXConstraint(expr.tok, "IntLikeOrBitvector", e.E1.Type, "type of right argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must be an integer-numeric or bitvector type");
            }
            break;

          case BinaryExpr.Opcode.Add: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "Plussable", expr.Type, "type of + must be of a numeric type, a bitvector type, ORDINAL, char, a sequence type, or a set-like or map-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to + ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to + ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
            }
            break;

          case BinaryExpr.Opcode.Sub: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "Minusable", expr.Type, "type of - must be of a numeric type, bitvector type, ORDINAL, char, or a set-like or map-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to - ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              // The following handles map subtraction, but does not in an unfortunately restrictive way.
              // First, it would be nice to delay the decision of it this is a map subtraction or not. This settles
              // for the simple way to decide based on what is currently known about the result type, which is also
              // done, for example, when deciding if "<" denotes rank ordering on datatypes.
              // Second, for map subtraction, it would be nice to allow the right-hand operand to be either a set or
              // an iset. That would also lead to further complexity in the code, so this code restricts the right-hand
              // operand to be a set.
              var eType = PartiallyResolveTypeForMemberSelection(expr.tok, expr.Type).AsMapType;
              if (eType != null) {
                // allow "map - set == map"
                var expected = new SetType(true, eType.Domain);
                ConstrainSubtypeRelation(expected, e.E1.Type, expr.tok, "map subtraction expects right-hand operand to have type {0} (instead got {1})", expected, e.E1.Type);
              } else {
                ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to - ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
              }
            }
            break;

          case BinaryExpr.Opcode.Mul: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "Mullable", expr.Type, "type of * must be of a numeric type, bitvector type, or a set-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to * ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to * ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
            }
            break;

          case BinaryExpr.Opcode.In:
          case BinaryExpr.Opcode.NotIn:
            AddXConstraint(expr.tok, "Innable", e.E1.Type, e.E0.Type, "second argument to \"" + BinaryExpr.OpcodeString(e.Op) + "\" must be a set, multiset, or sequence with elements of type {1}, or a map with domain {1} (instead got {0})");
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Div:
            expr.Type = new InferredTypeProxy();
            AddXConstraint(expr.tok, "NumericOrBitvector", expr.Type, "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be numeric or bitvector types (got {0})");
            ConstrainSubtypeRelation(expr.Type, e.E0.Type,
              expr, "type of left argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})",
              e.E0.Type, expr.Type);
            ConstrainSubtypeRelation(expr.Type, e.E1.Type,
              expr, "type of right argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})",
              e.E1.Type, expr.Type);
            break;

#endif
          case BinaryExpr.Opcode.Mod:
            expr.PreType = CreatePreTypeProxy();
            AddDefaultAdvice(expr.PreType, AdviceTarget.Int);
            AddConfirmation(expr.tok, "IntLikeOrBitvector", expr.PreType, "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be integer-numeric or bitvector types (got {0})");
            AddEqualityConstraint(expr.PreType, e.E0.PreType,
              expr, "type of left argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})");
            AddEqualityConstraint(expr.PreType, e.E1.PreType,
              expr, "type of right argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})");
            break;

#if SOON
          case BinaryExpr.Opcode.BitwiseAnd:
          case BinaryExpr.Opcode.BitwiseOr:
          case BinaryExpr.Opcode.BitwiseXor:
            expr.Type = NewIntegerBasedProxy(expr.tok);
            var errFormat = "first argument to " + BinaryExpr.OpcodeString(e.Op) + " must be of a bitvector type (instead got {0})";
            ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr, errFormat, e.E0.Type);
            AddXConstraint(expr.tok, "IsBitvector", e.E0.Type, errFormat);
            errFormat = "second argument to " + BinaryExpr.OpcodeString(e.Op) + " must be of a bitvector type (instead got {0})";
            ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr, errFormat, e.E1.Type);
            AddXConstraint(expr.tok, "IsBitvector", e.E1.Type, errFormat);
            break;
#endif

          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected operator
        }
        // We should also fill in e.ResolvedOp, but we may not have enough information for that yet.  So, instead, delay
        // setting e.ResolvedOp until inside CheckTypeInference.

#if SOON
      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        ResolveExpression(e.E0, opts);
        ResolveExpression(e.E1, opts);
        ResolveExpression(e.E2, opts);
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            AddXConstraint(expr.tok, "IntOrORDINAL", e.E0.Type, "prefix-equality limit argument must be an ORDINAL or integer expression (got {0})");
            AddXConstraint(expr.tok, "Equatable", e.E1.Type, e.E2.Type, "arguments must have the same type (got {0} and {1})");
            AddXConstraint(expr.tok, "IsCoDatatype", e.E1.Type, "arguments to prefix equality must be codatatypes (instead of {0})");
            expr.Type = Type.Bool;
            break;
          default:
            Contract.Assert(false);  // unexpected ternary operator
            break;
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, opts);
          }
          scope.PushMarker();
          if (e.LHSs.Count != e.RHSs.Count) {
            ReportError(expr, "let expression must have same number of LHSs (found {0}) as RHSs (found {1})", e.LHSs.Count, e.RHSs.Count);
          }
          var i = 0;
          foreach (var lhs in e.LHSs) {
            var rhsType = i < e.RHSs.Count ? e.RHSs[i].Type : new InferredTypeProxy();
            ResolveCasePattern(lhs, rhsType, opts.codeContext);
            // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
            var c = 0;
            foreach (var v in lhs.Vars) {
              ScopePushAndReport(scope, v, "let-variable");
              c++;
            }
            if (c == 0) {
              // Every identifier-looking thing in the pattern resolved to a constructor; that is, this LHS is a constant literal
              ReportError(lhs.tok, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
            }
            i++;
          }
        } else {
          // let-such-that expression
          if (e.RHSs.Count != 1) {
            ReportError(expr, "let-such-that expression must have just one RHS (found {0})", e.RHSs.Count);
          }
          // the bound variables are in scope in the RHS of a let-such-that expression
          scope.PushMarker();
          foreach (var lhs in e.LHSs) {
            Contract.Assert(lhs.Var != null);  // the parser already checked that every LHS is a BoundVar, not a general pattern
            var v = lhs.Var;
            ScopePushAndReport(scope, v, "let-variable");
            ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            AddTypeDependencyEdges(opts.codeContext, v.Type);
          }
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, opts);
            ConstrainTypeExprBool(rhs, "type of RHS of let-such-that expression must be boolean (got {0})");
          }
        }
        ResolveExpression(e.Body, opts);
        ResolveAttributes(e.Attributes, e, opts);
        scope.PopMarker();
        expr.Type = e.Body.Type;
      } else if (expr is LetOrFailExpr) {
        var e = (LetOrFailExpr)expr;
        ResolveLetOrFailExpr(e, opts);
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        if (opts.codeContext is Function) {
          ((Function)opts.codeContext).ContainsQuantifier = true;
        }
        Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        bool _val = true;
        bool typeQuantifier = Attributes.ContainsBool(e.Attributes, "typeQuantifier", ref _val) && _val;
        allTypeParameters.PushMarker();
        ResolveTypeParameters(e.TypeArgs, true, e);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          var option = typeQuantifier ? new ResolveTypeOption(e) : new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies);
          ResolveType(v.tok, v.Type, opts.codeContext, option, typeQuantifier ? e.TypeArgs : null);
        }
        if (e.TypeArgs.Count > 0 && !typeQuantifier) {
          ReportError(expr, "a quantifier cannot quantify over types. Possible fix: use the experimental attribute :typeQuantifier");
        }
        if (e.Range != null) {
          ResolveExpression(e.Range, opts);
          ConstrainTypeExprBool(e.Range, "range of quantifier must be of type bool (instead got {0})");
        }
        ResolveExpression(e.Term, opts);
        ConstrainTypeExprBool(e.Term, "body of quantifier must be of type bool (instead got {0})");
        // Since the body is more likely to infer the types of the bound variables, resolve it
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(e.Attributes, e, opts);
        scope.PopMarker();
        allTypeParameters.PopMarker();
        expr.Type = Type.Bool;

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var inferredProxy = v.Type as InferredTypeProxy;
          if (inferredProxy != null) {
            Contract.Assert(!inferredProxy.KeepConstraints);  // in general, this proxy is inferred to be a base type
          }
        }
        ResolveExpression(e.Range, opts);
        ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
        ResolveExpression(e.Term, opts);

        ResolveAttributes(e.Attributes, e, opts);
        scope.PopMarker();
        expr.Type = new SetType(e.Finite, e.Term.Type);

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        Contract.Assert(e.BoundVars.Count == 1 || (1 < e.BoundVars.Count && e.TermLeft != null));
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var inferredProxy = v.Type as InferredTypeProxy;
          if (inferredProxy != null) {
            Contract.Assert(!inferredProxy.KeepConstraints);  // in general, this proxy is inferred to be a base type
          }
        }
        ResolveExpression(e.Range, opts);
        ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
        if (e.TermLeft != null) {
          ResolveExpression(e.TermLeft, opts);
        }
        ResolveExpression(e.Term, opts);

        ResolveAttributes(e.Attributes, e, opts);
        scope.PopMarker();
        expr.Type = new MapType(e.Finite, e.TermLeft != null ? e.TermLeft.Type : e.BoundVars[0].Type, e.Term.Type);

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, opts.codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }

        if (e.Range != null) {
          ResolveExpression(e.Range, opts);
          ConstrainTypeExprBool(e.Range, "Precondition must be boolean (got {0})");
        }
        foreach (var read in e.Reads) {
          ResolveFrameExpression(read, FrameExpressionUse.Reads, opts.codeContext);
        }
        ResolveExpression(e.Term, opts);
        scope.PopMarker();
        expr.Type = SelectAppropriateArrowType(e.tok, e.BoundVars.ConvertAll(v => v.Type), e.Body.Type, e.Reads.Count != 0, e.Range != null);
      } else if (expr is WildcardExpr) {
        expr.Type = new SetType(true, builtIns.ObjectQ());
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveStatement(e.S, opts.codeContext);
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          var r = e.S as UpdateStmt;
          if (r != null && r.ResolvedStatements.Count == 1) {
            var call = r.ResolvedStatements[0] as CallStmt;
            if (call.Method is TwoStateLemma && !opts.twoState) {
              ReportError(call, "two-state lemmas can only be used in two-state contexts");
            }
          }
        }
        ResolveExpression(e.E, opts);
        expr.Type = e.E.Type;

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        ResolveExpression(e.Test, opts);
        ResolveExpression(e.Thn, opts);
        ResolveExpression(e.Els, opts);
        ConstrainTypeExprBool(e.Test, "guard condition in if-then-else expression must be a boolean (instead got {0})");
        expr.Type = new InferredTypeProxy();
        ConstrainSubtypeRelation(expr.Type, e.Thn.Type, expr, "the two branches of an if-then-else expression must have the same type (got {0} and {1})", e.Thn.Type, e.Els.Type);
        ConstrainSubtypeRelation(expr.Type, e.Els.Type, expr, "the two branches of an if-then-else expression must have the same type (got {0} and {1})", e.Thn.Type, e.Els.Type);

      } else if (expr is MatchExpr) {
        ResolveMatchExpr((MatchExpr)expr, opts);
      } else if (expr is NestedMatchExpr) {
        NestedMatchExpr e = (NestedMatchExpr)expr;
        ResolveNestedMatchExpr(e, opts);
        if (e.ResolvedExpression != null && e.ResolvedExpression.Type != null) {
          // i.e. no error was thrown during compiling of the NextedMatchExpr or during resolution of the ResolvedExpression
          expr.Type = e.ResolvedExpression.Type;
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }

      if (expr.Type == null) {
        // some resolution error occurred
        expr.Type = new InferredTypeProxy();
#endif
      }
    }
    
    /// <summary>
    /// Resolve "memberName" in what currently is known as "receiverType". If "receiverType" is an unresolved
    /// proxy type, try to solve enough type constraints and use heuristics to figure out which type contains
    /// "memberName" and return that enclosing type as "tentativeReceiverType". However, try not to make
    /// type-inference decisions about "receiverType"; instead, lay down the further constraints that need to
    /// be satisfied in order for "tentativeReceiverType" to be where "memberName" is found.
    /// Consequently, if "memberName" is found and returned as a "MemberDecl", it may still be the case that
    /// "receiverType" is an unresolved proxy type and that, after solving more type constraints, "receiverType"
    /// eventually gets set to a type more specific than "tentativeReceiverType".
    /// </summary>
    MemberDecl FindMember(Bpl.IToken tok, Type receiverType, string memberName, out NonProxyType tentativeReceiverType) {
      Contract.Requires(tok != null);
      Contract.Requires(receiverType != null);
      Contract.Requires(memberName != null);
      Contract.Ensures(Contract.Result<MemberDecl>() == null || Contract.ValueAtReturn(out tentativeReceiverType) != null);

#if SOON
      receiverType = PartiallyResolveTypeForMemberSelection(tok, receiverType, memberName);

      if (receiverType is TypeProxy) {
        ReportError(tok, "type of the receiver is not fully determined at this program point", receiverType);
        tentativeReceiverType = null;
        return null;
      }
      Contract.Assert(receiverType is NonProxyType);  // there are only two kinds of types: proxies and non-proxies

      foreach (var valuet in valuetypeDecls) {
        if (valuet.IsThisType(receiverType)) {
          MemberDecl member;
          if (valuet.Members.TryGetValue(memberName, out member)) {
            SelfType resultType = null;
            if (member is SpecialFunction) {
              resultType = ((SpecialFunction)member).ResultType as SelfType;
            } else if (member is SpecialField) {
              resultType = ((SpecialField)member).Type as SelfType;
            }
            if (resultType != null) {
              SelfTypeSubstitution = new Dictionary<TypeParameter, Type>();
              SelfTypeSubstitution.Add(resultType.TypeArg, receiverType);
              resultType.ResolvedType = receiverType;
            }
            tentativeReceiverType = (NonProxyType)receiverType;
            return member;
          }
          break;
        }
      }

      var ctype = receiverType.NormalizeExpand() as UserDefinedType;
      var cd = ctype?.AsTopLevelTypeWithMembersBypassInternalSynonym;
      if (cd != null) {
        Contract.Assert(ctype.TypeArgs.Count == cd.TypeArgs.Count);  // follows from the fact that ctype was resolved
        MemberDecl member;
        if (!classMembers[cd].TryGetValue(memberName, out member)) {
          if (memberName == "_ctor") {
            ReportError(tok, "{0} {1} does not have an anonymous constructor", cd.WhatKind, cd.Name);
          } else {
            ReportError(tok, "member '{0}' does not exist in {2} '{1}'", memberName, cd.Name, cd.WhatKind);
          }
        } else if (!resolver.VisibleInScope(member)) {
          ReportError(tok, "member '{0}' has not been imported in this scope and cannot be accessed here", memberName);
        } else {
          tentativeReceiverType = ctype;
          return member;
        }
        tentativeReceiverType = null;
        return null;
      }

      ReportError(tok, "type {0} does not have a member {1}", receiverType, memberName);
#endif
      tentativeReceiverType = null;
      return null;
    }
  
    /// <summary>
    /// Look up expr.Name in the following order:
    ///  0. Local variable, parameter, or bound variable.
    ///     (Language design note:  If this clashes with something of interest, one can always rename the local variable locally.)
    ///  1. Member of enclosing class (an implicit "this" is inserted, if needed)
    ///  2. If isLastNameSegment:
    ///     Unambiguous constructor name of a datatype in the enclosing module (if two constructors have the same name, an error message is produced here)
    ///     (Language design note:  If the constructor name is ambiguous or if one of the steps above takes priority, one can qualify the constructor
    ///     name with the name of the datatype.)
    ///  3. Member of the enclosing module (type name or the name of a module)
    ///  4. Static function or method in the enclosing module or its imports
    ///  5. If !isLastNameSegment:
    ///     Unambiguous constructor name of a datatype in the enclosing module
    ///
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="isLastNameSegment">Indicates that the NameSegment is not directly enclosed in another NameSegment or ExprDotName expression.</param>
    /// <param name="args">If the NameSegment is enclosed in an ApplySuffix, then these are the arguments.  The method returns null to indicate
    /// that these arguments, if any, were not used.  If args is non-null and the method does use them, the method returns the resolved expression
    /// that incorporates these arguments.</param>
    /// <param name="opts"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a MemberSelectExpr whose .Member is a Method.</param>
    /// <param name="complain"></param>
    Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<ActualBinding> args,
      Resolver.ResolveOpts opts, bool allowMethodCall, bool complain = true) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(opts != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          resolver.ResolveType(expr.tok, ty, opts.codeContext, Resolver.ResolveTypeOptionEnum.InferTypeProxies, null);
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"

      // For 1 and 4:
      MemberDecl member = null;
      // For 2 and 5:
      Tuple<DatatypeCtor, bool> pair;

      var name = opts.isReveal ? "reveal_" + expr.Name : expr.Name;
      var v = scope.Find(name);
      if (v != null) {
        // ----- 0. local variable, parameter, or bound variable
        if (expr.OptTypeArguments != null) {
          if (complain) {
            ReportError(expr.tok, "variable '{0}' does not take any type parameters", name);
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        }
        r = new IdentifierExpr(expr.tok, v);
        r.PreType = Type2PreType(r.Type);
      } else if (currentClass is TopLevelDeclWithMembers cl && resolver.classMembers.TryGetValue(cl, out var members) &&
                 members.TryGetValue(name, out member)) {
        // ----- 1. member of the enclosing class
        Expression receiver;
        if (member.IsStatic) {
          receiver = new StaticReceiverExpr(expr.tok, UserDefinedType.FromTopLevelDecl(expr.tok, currentClass, currentClass.TypeArgs),
            (TopLevelDeclWithMembers)member.EnclosingClass, true);
        } else {
          if (!scope.AllowInstance) {
            if (complain) {
              ReportError(expr.tok, "'this' is not allowed in a 'static' context"); //TODO: Rephrase this
            } else {
              expr.ResolvedExpression = null;
              return null;
            }
            // nevertheless, set "receiver" to a value so we can continue resolution
          }
          receiver = new ImplicitThisExpr(expr.tok);
          receiver.Type = Resolver.GetThisType(expr.tok, currentClass);
          receiver.PreType = Type2PreType(receiver.Type);
        }
        r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, opts, allowMethodCall);
#if SOON
      } else if (isLastNameSegment && resolver.moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 2. datatype constructor
        if (ResolveDatatypeConstructor(expr, args, opts, complain, pair, name, ref r, ref rWithArgs)) {
          return null;
        }
      } else if (resolver.moduleInfo.TopLevels.TryGetValue(name, out var decl)) {
        // ----- 3. Member of the enclosing module
        if (decl is AmbiguousTopLevelDecl ambiguousTopLevelDecl) {
          if (complain) {
            ReportError(expr.tok,
              "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)",
              expr.Name, ambiguousTopLevelDecl.ModuleNames());
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        } else {
          // We have found a module name or a type name, neither of which is an expression. However, the NameSegment we're
          // looking at may be followed by a further suffix that makes this into an expresion. We postpone the rest of the
          // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
          // or verifier, just to have a placeholder where we can recorded what we have found.
          if (!isLastNameSegment) {
            if (decl is ClassDecl cd && cd.NonNullTypeDecl != null && name != cd.NonNullTypeDecl.Name) {
              // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
              // the name of the class, C. Report an error and continue.
              if (complain) {
                ReportError(expr.tok, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
              } else {
                expr.ResolvedExpression = null;
                return null;
              }
            }
          }
          r = CreateResolver_IdentifierExpr(expr.tok, name, expr.OptTypeArguments, decl);
        }

      } else if (resolver.moduleInfo.StaticMembers.TryGetValue(name, out member)) {
        // ----- 4. static member of the enclosing module
        Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
        if (member is AmbiguousMemberDecl ambiguousMember) {
          if (complain) {
            ReportError(expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.Name, ambiguousMember.ModuleNames());
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        } else {
          var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass, true);
          r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, opts, allowMethodCall);
        }

      } else if (!isLastNameSegment && resolver.moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 5. datatype constructor
        if (ResolveDatatypeConstructor(expr, args, opts, complain, pair, name, ref r, ref rWithArgs)) {
          return null;
        }
#endif

      } else {
        // ----- None of the above
        if (complain) {
          ReportError(expr.tok, "unresolved identifier: {0}", name);
        } else {
          expr.ResolvedExpression = null;
          return null;
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .PreType
        expr.PreType = CreatePreTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type.UseInternalSynonym();
        expr.PreType = Type2PreType(expr.Type);
      }
      return rWithArgs;
    }

    Expression ResolveExprDotCall(IToken tok, Expression receiver, Type receiverTypeBound/*?*/,
      MemberDecl member, List<ActualBinding> args, List<Type> optTypeArguments, Resolver.ResolveOpts opts, bool allowMethodCall) {
      Contract.Requires(tok != null);
      Contract.Requires(receiver != null);
      Contract.Requires(receiver.WasResolved());
      Contract.Requires(member != null);
      Contract.Requires(opts != null && opts.codeContext != null);

      var rr = new MemberSelectExpr(tok, receiver, member.Name);
      rr.Member = member;

#if SOON
      // Now, fill in rr.Type.  This requires taking into consideration the type parameters passed to the receiver's type as well as any type
      // parameters used in this NameSegment/ExprDotName.
      // Add to "subst" the type parameters given to the member's class/datatype
      rr.TypeApplication_AtEnclosingClass = new List<Type>();
      rr.TypeApplication_JustMember = new List<Type>();
      Dictionary<TypeParameter, Type> subst;
      var rType = (receiverTypeBound ?? receiver.Type).NormalizeExpand();
      if (rType is UserDefinedType udt && udt.ResolvedClass != null) {
        subst = Resolver.TypeSubstitutionMap(udt.ResolvedClass.TypeArgs, udt.TypeArgs);
        if (member.EnclosingClass == null) {
          // this can happen for some special members, like real.Floor
        } else {
          rr.TypeApplication_AtEnclosingClass.AddRange(rType.AsParentType(member.EnclosingClass).TypeArgs);
        }
      } else {
        var vtd = AsValuetypeDecl(rType);
        if (vtd != null) {
          Contract.Assert(vtd.TypeArgs.Count == rType.TypeArgs.Count);
          subst = Resolver.TypeSubstitutionMap(vtd.TypeArgs, rType.TypeArgs);
          rr.TypeApplication_AtEnclosingClass.AddRange(rType.TypeArgs);
        } else {
          Contract.Assert(rType.TypeArgs.Count == 0);
          subst = new Dictionary<TypeParameter, Type>();
        }
      }

      if (member is Field) {
        var field = (Field)member;
        if (optTypeArguments != null) {
          ReportError(tok, "a field ({0}) does not take any type arguments (got {1})", field.Name, optTypeArguments.Count);
        }
        subst = BuildTypeArgumentSubstitute(subst, receiverTypeBound ?? receiver.Type);
        rr.Type = SubstType(field.Type, subst);
        AddCallGraphEdgeForField(opts.codeContext, field, rr);
      } else if (member is Function) {
        var fn = (Function)member;
        if (fn is TwoStateFunction && !opts.twoState) {
          ReportError(tok, "two-state function ('{0}') can only be called in a two-state context", member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != fn.TypeArgs.Count) {
          ReportError(tok, "function '{0}' expects {1} type argument{2} (got {3})",
            member.Name, fn.TypeArgs.Count, Util.Plural(fn.TypeArgs.Count), suppliedTypeArguments);
        }
        for (int i = 0; i < fn.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? optTypeArguments[i] : new InferredTypeProxy();
          rr.TypeApplication_JustMember.Add(ta);
          subst.Add(fn.TypeArgs[i], ta);
        }
        subst = BuildTypeArgumentSubstitute(subst, receiverTypeBound ?? receiver.Type);
        rr.Type = SelectAppropriateArrowType(fn.tok,
          fn.Formals.ConvertAll(f => SubstType(f.Type, subst)),
          SubstType(fn.ResultType, subst),
          fn.Reads.Count != 0, fn.Req.Count != 0);
        AddCallGraphEdge(opts.codeContext, fn, rr, IsFunctionReturnValue(fn, args, opts));
      } else {
        // the member is a method
        var m = (Method)member;
        if (!allowMethodCall) {
          // it's a method and method calls are not allowed in the given context
          ReportError(tok, "expression is not allowed to invoke a {0} ({1})", member.WhatKind, member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != m.TypeArgs.Count) {
          ReportError(tok, "method '{0}' expects {1} type argument{2} (got {3})",
            member.Name, m.TypeArgs.Count, Util.Plural(m.TypeArgs.Count), suppliedTypeArguments);
        }
        for (int i = 0; i < m.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? optTypeArguments[i] : new InferredTypeProxy();
          rr.TypeApplication_JustMember.Add(ta);
          subst.Add(m.TypeArgs[i], ta);
        }
        subst = BuildTypeArgumentSubstitute(subst, receiverTypeBound ?? receiver.Type);
        rr.ResolvedOutparameterTypes = m.Outs.ConvertAll(f => SubstType(f.Type, subst));
        rr.Type = new InferredTypeProxy();  // fill in this field, in order to make "rr" resolved
      }
#endif
      return rr;
    }
    
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
    
    void CheckTypeInference(Expression expr, ICodeContext codeContext) {
      Contract.Requires(expr != null);
      Contract.Requires(codeContext != null);
      PartiallySolveTypeConstraints();
      var c = new Resolver.CheckTypeInference_Visitor(resolver, codeContext);
      c.Visit(expr);
    }
    
    // ---------------------------------------- Migration sanity checks ----------------------------------------

    public void SanityCheckOldAndNewInference(List<TopLevelDecl> declarations) {
      var visitor = new PreTypeSanityChecker(this);
      foreach (var decl in declarations) {
        foreach (var attr in decl.Attributes.AsEnumerable()) {
          visitor.Visit(attr.Args);
        }
        if (decl is RedirectingTypeDecl rtd) {
          if (rtd.Constraint != null) {
            visitor.Visit(rtd.Constraint);
          }
          if (rtd.Witness != null) {
            visitor.Visit(rtd.Witness);
          }
        } else if (decl is IteratorDecl iter) {
          visitor.Visit(iter);
        } else if (decl is TopLevelDeclWithMembers md) {
          foreach (var member in md.Members) {
            if (member is ConstantField cfield && cfield.Rhs != null) {
              visitor.Visit(cfield.Rhs);
            } else if (member is Function f) {
              visitor.Visit(f);
              if (f is ExtremePredicate extremePredicate) {
                visitor.Visit(extremePredicate.PrefixPredicate);
              }
            } else if (member is Method m) {
              visitor.Visit(m);
              if (m is ExtremeLemma extremeLemma) {
                visitor.Visit(extremeLemma.PrefixLemma);
              }
            }
          }        
        }
      }
    }

    class PreTypeSanityChecker : BottomUpVisitor {
      private PreTypeResolver preTypeResolver;

      public PreTypeSanityChecker(PreTypeResolver preTypeResolver) {
        this.preTypeResolver = preTypeResolver;
      }
      
      protected override void VisitOneExpr(Expression expr) {
        // compare expr.PreType and expr.Type
        if (expr.PreType == null) {
          preTypeResolver.ReportWarning(expr.tok, $"sanity check WARNING: no pre-type was computed");
        } else {
          var pt0 = expr.PreType.Normalize();
          var pt1 = preTypeResolver.Type2PreType(expr.Type).Normalize();
          if (!pt0.Same(pt1)) {
            preTypeResolver.ReportError(expr.tok, $"SANITY CHECK FAILED: pre-type '{pt0}' does not correspond to type '{expr.Type}'");
          }
        }
      }
    }
  }
}
