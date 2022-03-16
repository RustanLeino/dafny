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
    // ---------------------------------------- Expressions ----------------------------------------

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
        ResolveExpression(e.E, new Resolver.ResolveOpts(opts.codeContext, false, opts.isReveal, opts.isPostCondition, true));
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

  }
}
