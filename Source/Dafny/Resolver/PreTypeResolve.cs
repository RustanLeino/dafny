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
    private readonly Resolver resolver;
    private readonly Scope<TypeParameter> allTypeParameters = new();
    private readonly Scope<IVariable> scope = new();

    TopLevelDeclWithMembers currentClass;
    Method currentMethod;

    private int ErrorCount => resolver.Reporter.Count(ErrorLevel.Error);

    private void ReportError(Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      ReportError(d.tok, msg, args);
    }

    private void ReportError(Statement stmt, string msg, params object[] args) {
      Contract.Requires(stmt != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      ReportError(stmt.Tok, msg, args);
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
      resolver.Reporter.Error(MessageSource.Resolver, tok, "PRE-TYPE: " + msg, args);
    }
    
    private void ReportWarning(Bpl.IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      resolver.Reporter.Warning(MessageSource.Resolver, tok, msg, args);
    }

    private readonly Dictionary<string, TopLevelDecl> preTypeBuiltins = new();

    TopLevelDecl BuiltInTypeDecl(string name) {
      Contract.Requires(name != null);
      if (preTypeBuiltins.TryGetValue(name, out var decl)) {
        return decl;
      }
      if (IsArrayName(name, out var dims)) {
        // make sure the array class has been created
        var at = resolver.builtIns.ArrayType(Token.NoToken, dims,
          new List<Type> { new InferredTypeProxy() }, true);
        decl = resolver.builtIns.arrayTypeDecls[dims];
      } else if (IsBitvectorName(name, out var width)) {
        var bvDecl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, 0, t => t.IsBitVectorType, null);
        var bvType = new BitvectorType(width);
        resolver.AddRotateMember(bvDecl, "RotateLeft", new SelfType());
        resolver.AddRotateMember(bvDecl, "RotateRight", new SelfType());
        decl = bvDecl;
      } else {
        foreach (var valueTypeDecl in resolver.valuetypeDecls) {
          if (valueTypeDecl.Name == name) {
            // bool, int, real, ORDINAL, map, imap
            decl = valueTypeDecl;
            break;
          }
        }
        if (decl == null) {
          var typeParameterCount = name == "set" || name == "iset" || name == "seq" || name == "multiset" ? 1 : 0;
          decl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, typeParameterCount, _ => false, null);
        }
      }
      preTypeBuiltins.Add(name, decl);
      return decl;
    }

    TopLevelDecl BuiltInArrowTypeDecl(int arity) {
      Contract.Requires(0 <= arity);
      var name = $"~>{arity}";
      if (!preTypeBuiltins.TryGetValue(name, out var decl)) {
        decl = new ValuetypeDecl(name, resolver.builtIns.SystemModule, arity + 1, _ => false, null);
        preTypeBuiltins.Add(name, decl);
      }
      return decl;
    }

    private int typeProxyCount = 0; // used to give each PreTypeProxy a unique ID

    private readonly List<(PreTypeProxy, string)> allPreTypeProxies = new();

    public PreType CreatePreTypeProxy(string description = null) {
      var proxy = new PreTypeProxy(typeProxyCount++);
      allPreTypeProxies.Add((proxy, description));
      return proxy;
    }

    public PreType Type2PreType(Type type, string description = null, Type printableType = null) {
      Contract.Requires(type != null);

      printableType ??= type.Normalize();
      type = type.NormalizeExpand();
      if (type is BoolType) {
        return new DPreType(BuiltInTypeDecl("bool"), this, printableType);
      } else if (type is CharType) {
        return new DPreType(BuiltInTypeDecl("char"), this, printableType);
      } else if (type is IntType) {
        return new DPreType(BuiltInTypeDecl("int"), this, printableType);
      } else if (type is RealType) {
        return new DPreType(BuiltInTypeDecl("real"), this, printableType);
      } else if (type is BigOrdinalType) {
        return new DPreType(BuiltInTypeDecl("ORDINAL"), this, printableType);
      } else if (type is BitvectorType bitvectorType) {
        return new DPreType(BuiltInTypeDecl("bv" + bitvectorType.Width), this, printableType);
      } else if (type is CollectionType) {
        var name =
          type is SetType st ? (st.Finite ? "set" : "iset") :
          type is MultiSetType ? "multiset" :
          type is MapType mt ? (mt.Finite ? "map" : "imap") :
          "seq";
        var args = type.TypeArgs.ConvertAll(ty => Type2PreType(ty));
        return new DPreType(BuiltInTypeDecl(name), args, printableType);
      } else if (type is ArrowType at) {
        var args = type.TypeArgs.ConvertAll(ty => Type2PreType(ty));
        return new DPreType(BuiltInArrowTypeDecl(at.Arity), args);
      } else if (type is UserDefinedType udt) {
        var args = type.TypeArgs.ConvertAll(ty => Type2PreType(ty));
        return new DPreType(udt.ResolvedClass, args);
      } else if (type is TypeProxy) {
        return CreatePreTypeProxy(description);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }


    /// <summary>
    /// Returns the non-newtype ancestor of "cecl".
    /// </summary>
    public TopLevelDecl AncestorDecl(TopLevelDecl decl) {
      while (decl is NewtypeDecl newtypeDecl) {
        var parent = newtypeDecl.BasePreType.Normalize();
        decl = ((DPreType)parent).Decl;
      }
      return decl;
    }

    /// <summary>
    /// Returns the non-newtype ancestor of "preType".
    /// </summary>
    public DPreType NewTypeAncestor(DPreType preType) {
      Contract.Requires(preType != null);
      while (preType.Decl is NewtypeDecl newtypeDecl) {
        var parent = newtypeDecl.BasePreType.Normalize() as DPreType;
        if (parent == null) {
          // The parent type of this newtype apparently hasn't been inferred yet, so stop traversal here
          break;
        }
        var subst = PreType.PreTypeSubstMap(newtypeDecl.TypeArgs, preType.Arguments);
        preType = (DPreType)parent.Substitute(subst);
      }
      return preType;
    }

    public static bool IsBitvectorName(string name, out int width) {
      Contract.Requires(name != null);
      if (name.StartsWith("bv")) {
        var bits = name.Substring(2);
        width = 0; // set to 0, in case the first disjunct of the next line evaluates to true
        return bits == "0" || (bits.Length != 0 && bits[0] != '0' && int.TryParse(bits, out width));
      }
      width = 0; // unused by caller
      return false;
    }

    public static bool IsBitvectorName(string name) {
      return IsBitvectorName(name, out _);
    }

    public static bool IsArrayName(string name, out int dimensions) {
      Contract.Requires(name != null);
      if (name.StartsWith("array")) {
        var dims = name.Substring(5);
        if (dims.Length == 0) {
          dimensions = 1;
          return true;
        } else if (dims[0] != '0' && dims != "1" && int.TryParse(dims, out dimensions)) {
          return true;
        }
      }
      dimensions = 0; // unused by caller
      return false;
    }

    public PreTypeResolver(Resolver resolver) {
      Contract.Requires(resolver != null);
      this.resolver = resolver;
    }

    void ScopePushAndReport(IVariable v, string kind) {
      Contract.Requires(scope != null);
      Contract.Requires(v != null);
      Contract.Requires(kind != null);
      v.PreType = Type2PreType(v.Type);
      ScopePushAndReport(scope, v.Name, v, v.Tok, kind);
    }

    void ScopePushExpectSuccess(IVariable v, string kind) {
      Contract.Requires(scope != null);
      Contract.Requires(v != null);
      Contract.Requires(kind != null);
      v.PreType = Type2PreType(v.Type);
      var r = ScopePushAndReport(scope, v.Name, v, v.Tok, kind);
      Contract.Assert(r == Scope<IVariable>.PushResult.Success);
    }

    private Scope<Thing>.PushResult ScopePushAndReport<Thing>(Scope<Thing> scope, string name, Thing thing, IToken tok, string kind) where Thing : class {
      Contract.Requires(scope != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      Contract.Requires(tok != null);
      Contract.Requires(kind != null);
      var r = scope.Push(name, thing);
      switch (r) {
        case Scope<Thing>.PushResult.Success:
          break;
        case Scope<Thing>.PushResult.Duplicate:
          ReportError(tok, "Duplicate {0} name: {1}", kind, name);
          break;
        case Scope<Thing>.PushResult.Shadow:
          ReportWarning(tok, "Shadowed {0} name: {1}", kind, name);
          break;
      }
      return r;
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
          ResolveAttributes(d, new Resolver.ResolveOpts(new NoContext(d.EnclosingModuleDefinition), false), true);
        }

        if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          if (dd.Var == null) {
            Contract.Assert(dd.Constraint == null); // follows from NewtypeDecl invariant
            Contract.Assert(dd.BaseType != null); // this should have been set by the parser
            Contract.Assert(dd.BasePreType == null); // this is about to be set here
            dd.BasePreType = Type2PreType(dd.BaseType);
          } else {
            Contract.Assert(object.ReferenceEquals(dd.Var.Type, dd.BaseType)); // follows from NewtypeDecl invariant
            Contract.Assert(dd.Var.PreType == null); // this is about to be set here
            dd.Var.PreType = Type2PreType(dd.Var.Type);
            dd.BasePreType = dd.Var.PreType;
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
            ResolveAttributes(ctor, new Resolver.ResolveOpts(new NoContext(d.EnclosingModuleDefinition), false), true);
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
            ctor.Formals.ForEach(p => ScopePushAndReport(p, "destructor"));
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
    
    void ResolveAttributes(IAttributeBearingDeclaration attributeHost, Resolver.ResolveOpts opts, bool solveConstraints) {
      Contract.Requires(attributeHost != null);
      Contract.Requires(opts != null);

      // order does not matter much for resolution, so resolve them in reverse order
      foreach (var attr in attributeHost.Attributes.AsEnumerable()) {
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
      ScopePushExpectSuccess(dd.Var, dd.WhatKind + " variable");

      ResolveExpression(dd.Constraint, new Resolver.ResolveOpts(new CodeContextWrapper(dd, true), false));
      ConstrainTypeExprBool(dd.Constraint, dd.WhatKind + " constraint must be of type bool (instead got {0})");
      SolveAllTypeConstraints($"{dd.WhatKind} '{dd.Name}' constraint");

      if (dd.Witness != null) {
        var prevErrCnt = ErrorCount;
        var codeContext = new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost);
        ResolveExpression(dd.Witness, new Resolver.ResolveOpts(codeContext, false));
        AddSubtypeConstraint(dd.Var.PreType, dd.Witness.PreType, dd.Witness.tok, "witness expression must have type '{0}' (got '{1}')");
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
          AddSubtypeConstraint(Type2PreType(formal.Type), Type2PreType(d.Type), d.tok, "default-value expression (of type '{1}') is not assignable to formal (of type '{0}')");
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
        ResolveAttributes(cfield, opts, true);
        if (cfield.Rhs != null) {
          ResolveExpression(cfield.Rhs, opts);
        }
        
      } else if (member is Field) {
        var opts = new Resolver.ResolveOpts(new NoContext(currentClass.EnclosingModuleDefinition), false);
        ResolveAttributes(member, opts, true);
        
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
      iter.Ins.ForEach(p => ScopePushAndReport(p, "in-parameter"));
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
        AddSubtypeConstraint(Type2PreType(d.Type), e.PreType, e.tok, "type of field '" + d.Name + "' is {1}, but has been constrained elsewhere to be of type {0}");
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

      ResolveAttributes(iter, new Resolver.ResolveOpts(iter, false), true);

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
        ScopePushAndReport(p, "parameter");
      }
      ResolveAttributes(f, new Resolver.ResolveOpts(f, false), true);
      // take care of the warnShadowing attribute
      if (Attributes.ContainsBool(f.Attributes, "warnShadowing", ref warnShadowing)) {
        DafnyOptions.O.WarnShadowing = warnShadowing;  // set the value according to the attribute
      }
      ResolveParameterDefaultValues(f.Formals, f);
      foreach (AttributedExpression e in f.Req) {
        ResolveAttributes(e, new Resolver.ResolveOpts(f, f is TwoStateFunction), false);
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
          ScopePushAndReport(f.Result, "function result"); // function return only visible in post-conditions
        }
        ResolveExpression(r, new Resolver.ResolveOpts(f, f is TwoStateFunction, false, true, false));  // since this is a function, the postcondition is still a one-state predicate, unless it's a two-state function
        ConstrainTypeExprBool(r, "Postcondition must be a boolean (got {0})");
        if (f.Result != null) {
          scope.PopMarker();
        }
      }
      ResolveAttributes(f.Decreases, new Resolver.ResolveOpts(f, f is TwoStateFunction), false);
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
        AddSubtypeConstraint(Type2PreType(f.ResultType), f.Body.PreType, f.tok, "Function body type mismatch (expected {0}, got {1})");
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
          ScopePushAndReport(p, "in-parameter");
        }
        ResolveParameterDefaultValues(m.Ins, m);

        // Start resolving specification...
        foreach (AttributedExpression e in m.Req) {
          ResolveAttributes(e, new Resolver.ResolveOpts(m, m is TwoStateLemma), false);
          ResolveExpression(e.E, new Resolver.ResolveOpts(m, m is TwoStateLemma));
          ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
        }

        ResolveAttributes(m.Mod, new Resolver.ResolveOpts(m, false), false);
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
        ResolveAttributes(m.Decreases, new Resolver.ResolveOpts(m, false), false);
        foreach (Expression e in m.Decreases.Expressions) {
          ResolveExpression(e, new Resolver.ResolveOpts(m, m is TwoStateLemma));
          // any type is fine
        }

        if (m is Constructor) {
          scope.PopMarker();
          // start the scope again, but this time allowing instance
          scope.PushMarker();
          foreach (Formal p in m.Ins) {
            ScopePushAndReport(p, "in-parameter");
          }
        }

        // Add out-parameters to a new scope that will also include the outermost-level locals of the body
        // Don't care about any duplication errors among the out-parameters, since they have already been reported
        scope.PushMarker();
        if (m is ExtremeLemma && m.Outs.Count != 0) {
          ReportError(m.Outs[0].tok, "{0}s are not allowed to have out-parameters", m.WhatKind);
        } else {
          foreach (Formal p in m.Outs) {
            ScopePushAndReport(p, "out-parameter");
          }
        }

        // ... continue resolving specification
        foreach (AttributedExpression e in m.Ens) {
          ResolveAttributes(e, new Resolver.ResolveOpts(m, true), false);
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
            ScopePushExpectSuccess(k, "_k parameter");
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
        ResolveAttributes(m, new Resolver.ResolveOpts(m, m is TwoStateLemma), true);

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
        var (member, tentativeReceiverType) = FindMember(fe.E.tok, Type2PreType(eventualRefType), fe.FieldName);
        Contract.Assert((member == null) == (tentativeReceiverType == null)); // follows from contract of FindMember
        if (member == null) {
          // error has already been reported by FindMember
        } else if (!(member is Field)) {
          ReportError(fe.E, "member {0} in type {1} does not refer to a field", fe.FieldName, tentativeReceiverType.Decl.Name);
        } else if (member is ConstantField) {
          ReportError(fe.E, "expression is not allowed to refer to constant field {0}", fe.FieldName);
        } else {
          fe.Field = (Field)member;
        }
      }
    }

    void CheckTypeInference(Expression expr, ICodeContext codeContext) {
      Contract.Requires(expr != null);
      Contract.Requires(codeContext != null);
      PartiallySolveTypeConstraints();
      var c = new Resolver.CheckTypeInference_Visitor(resolver, codeContext);
      c.Visit(expr);
    }
    
    // ---------------------------------------- Utilities ----------------------------------------

    public Dictionary<TypeParameter, PreType> BuildPreTypeArgumentSubstitute(Dictionary<TypeParameter, PreType> typeArgumentSubstitutions, DPreType/*?*/ receiverTypeBound = null) {
      Contract.Requires(typeArgumentSubstitutions != null);

      var subst = new Dictionary<TypeParameter, PreType>();
      foreach (var entry in typeArgumentSubstitutions) {
        subst.Add(entry.Key, entry.Value);
      }

#if SOON
      if (SelfTypeSubstitution != null) {
        foreach (var entry in SelfTypeSubstitution) {
          subst.Add(entry.Key, entry.Value);
        }
      }
#endif

#if SOON
      if (receiverTypeBound != null) {
        TopLevelDeclWithMembers cl;
        var udt = receiverTypeBound?.AsNonNullRefType;
        if (udt != null) {
          cl = (TopLevelDeclWithMembers)((NonNullTypeDecl)udt.ResolvedClass).ViewAsClass;
        } else {
          udt = receiverTypeBound.NormalizeExpand() as UserDefinedType;
          cl = udt?.ResolvedClass as TopLevelDeclWithMembers;
        }
        if (cl != null) {
          foreach (var entry in cl.ParentFormalTypeParametersToActuals) {
            var v = entry.Value.Substitute(subst);
            subst.Add(entry.Key, v);
          }
        }
      }
#endif

      return subst;
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
          if (!PreType.Same(expr.PreType, preTypeResolver.Type2PreType(expr.Type))) {
            preTypeResolver.ReportError(expr.tok, $"SANITY CHECK FAILED: pre-type '{expr.PreType}' does not correspond to type '{expr.Type}'");
          }
        }
      }
    }
  }
}
