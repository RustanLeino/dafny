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
    private Scope<Statement> enclosingStatementLabels = new();
    private readonly Scope<Label> dominatingStatementLabels = new();
    private List<Statement> loopStack = new();  // the enclosing loops (from which it is possible to break out)
    bool inBodyInitContext;  // "true" only if "currentMethod is Constructor"

    void ResolveBlockStatement(BlockStmt blockStmt, ICodeContext codeContext) {
      Contract.Requires(blockStmt != null);
      Contract.Requires(codeContext != null);

      if (blockStmt is DividedBlockStmt div) {
        Contract.Assert(currentMethod is Constructor);  // divided bodies occur only in class constructors
        Contract.Assert(!inBodyInitContext);  // divided bodies are never nested
        inBodyInitContext = true;
        foreach (Statement ss in div.BodyInit) {
          ResolveStatementWithLabels(ss, codeContext);
        }
        Contract.Assert(inBodyInitContext);
        inBodyInitContext = false;
        foreach (Statement ss in div.BodyProper) {
          ResolveStatementWithLabels(ss, codeContext);
        }
      } else {
        foreach (Statement ss in blockStmt.Body) {
          ResolveStatementWithLabels(ss, codeContext);
        }
      }
    }

    void ResolveStatementWithLabels(Statement stmt, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);

      enclosingStatementLabels.PushMarker();
      // push labels
      for (var l = stmt.Labels; l != null; l = l.Next) {
        var lnode = l.Data;
        Contract.Assert(lnode.Name != null);  // LabelNode's with .Label==null are added only during resolution of the break statements with 'stmt' as their target, which hasn't happened yet
        var prev = enclosingStatementLabels.Find(lnode.Name);
        if (prev == stmt) {
          ReportError(lnode.Tok, "duplicate label");
        } else if (prev != null) {
          ReportError(lnode.Tok, "label shadows an enclosing label");
        } else {
          var r = enclosingStatementLabels.Push(lnode.Name, stmt);
          Contract.Assert(r == Scope<Statement>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          if (dominatingStatementLabels.Find(lnode.Name) != null) {
            ReportError(lnode.Tok, "label shadows a dominating label");
          } else {
            var rr = dominatingStatementLabels.Push(lnode.Name, lnode);
            Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          }
        }
      }
      ResolveStatement(stmt, codeContext);
      enclosingStatementLabels.PopMarker();
    }

    public void ResolveStatement(Statement stmt, ICodeContext codeContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(codeContext != null);

      if (!(stmt is ForallStmt || stmt is ForLoopStmt)) {  // "forall" and "for" statements do their own attribute resolution below
        ResolveAttributes(stmt, new Resolver.ResolveOpts(codeContext, true), false);
      }
      if (stmt is PredicateStmt) {
        var s = (PredicateStmt)stmt;
        var assertStmt = stmt as AssertStmt;
        if (assertStmt != null && assertStmt.Label != null) {
          if (dominatingStatementLabels.Find(assertStmt.Label.Name) != null) {
            ReportError(assertStmt.Label.Tok, "assert label shadows a dominating label");
          } else {
            var rr = dominatingStatementLabels.Push(assertStmt.Label.Name, assertStmt.Label);
            Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          }
        }
        ResolveExpression(s.Expr, new Resolver.ResolveOpts(codeContext, true));
        ConstrainTypeExprBool(s.Expr, "condition is expected to be of type bool, but is {0}");
        if (assertStmt != null && assertStmt.Proof != null) {
          // clear the labels for the duration of checking the proof body, because break statements are not allowed to leave a the proof body
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          ResolveStatement(assertStmt.Proof, codeContext);
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;
        }
        if (stmt is ExpectStmt expectStmt) {
          if (expectStmt.Message == null) {
            expectStmt.Message = new StringLiteralExpr(s.Tok, "expectation violation", false);
          }
          ResolveExpression(expectStmt.Message, new Resolver.ResolveOpts(codeContext, true));
        }

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        var opts = new Resolver.ResolveOpts(codeContext, false);
        s.Args.Iter(e => ResolveExpression(e, opts));

#if SOON
      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        foreach (var expr in s.Exprs) {
          var name = RevealStmt.SingleName(expr);
          var labeledAssert = name == null ? null : dominatingStatementLabels.Find(name) as AssertLabel;
          if (labeledAssert != null) {
            s.LabeledAsserts.Add(labeledAssert);
          } else {
            var opts = new Resolver.ResolveOpts(codeContext, codeContext is Method || codeContext is TwoStateFunction, true, false, false);
            if (expr is ApplySuffix) {
              var e = (ApplySuffix)expr;
              var methodCallInfo = ResolveApplySuffix(e, opts, true);
              if (methodCallInfo == null) {
                ReportError(expr.tok, "expression has no reveal lemma");
              } else if (methodCallInfo.Callee.Member is TwoStateLemma && !opts.twoState) {
                ReportError(methodCallInfo.Tok, "a two-state function can only be revealed in a two-state context");
              } else if (methodCallInfo.Callee.AtLabel != null) {
                Contract.Assert(methodCallInfo.Callee.Member is TwoStateLemma);
                ReportError(methodCallInfo.Tok, "to reveal a two-state function, do not list any parameters or @-labels");
              } else {
                var call = new CallStmt(methodCallInfo.Tok, s.EndTok, new List<Expression>(), methodCallInfo.Callee, methodCallInfo.ActualParameters);
                s.ResolvedStatements.Add(call);
              }
            } else {
              ResolveExpression(expr, opts);
            }
          }
        }
        foreach (var a in s.ResolvedStatements) {
          ResolveStatement(a, codeContext);
        }
#endif

      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          Statement target = enclosingStatementLabels.Find(s.TargetLabel.val);
          if (target == null) {
            ReportError(s.TargetLabel, $"{s.Kind} label is undefined or not in scope: {s.TargetLabel.val}");
          } else if (s.IsContinue && !(target is LoopStmt)) {
            ReportError(s.TargetLabel, $"continue label must designate a loop: {s.TargetLabel.val}");
          } else {
            s.TargetStmt = target;
          }
        } else {
          Contract.Assert(1 <= s.BreakAndContinueCount); // follows from BreakStmt class invariant and the guard for this "else" branch
          var jumpStmt = s.BreakAndContinueCount == 1 ?
            $"a non-labeled '{s.Kind}' statement" :
            $"a '{Util.Repeat(s.BreakAndContinueCount - 1, "break ")}{s.Kind}' statement";
          if (loopStack.Count == 0) {
            ReportError(s, $"{jumpStmt} is allowed only in loops");
          } else if (loopStack.Count < s.BreakAndContinueCount) {
            ReportError(s,
              $"{jumpStmt} is allowed only in contexts with {s.BreakAndContinueCount} enclosing loops, but the current context only has {loopStack.Count}");
          } else {
            Statement target = loopStack[loopStack.Count - s.BreakAndContinueCount];
            if (target.Labels == null) {
              // make sure there is a label, because the compiler and translator will want to see a unique ID
              target.Labels = new LList<Label>(new Label(target.Tok, null), null);
            }
            s.TargetStmt = target;
          }
        }

      } else if (stmt is ProduceStmt) {
        var kind = stmt is YieldStmt ? "yield" : "return";
        if (stmt is YieldStmt && !(codeContext is IteratorDecl)) {
          ReportError(stmt, "yield statement is allowed only in iterators");
        } else if (stmt is ReturnStmt && !(codeContext is Method)) {
          ReportError(stmt, "return statement is allowed only in method");
        } else if (inBodyInitContext) {
          ReportError(stmt, "return statement is not allowed before 'new;' in a constructor");
        }
        var s = (ProduceStmt)stmt;
        if (s.rhss == null) {
          // this is a regular return/yield statement.
          s.hiddenUpdate = null;
        } else {
          var cmc = codeContext as IMethodCodeContext;
          if (cmc == null) {
            // an error has already been reported above
          } else if (cmc.Outs.Count != s.rhss.Count) {
            ReportError(s, "number of {2} parameters does not match declaration (found {0}, expected {1})", s.rhss.Count, cmc.Outs.Count, kind);
          } else {
            Contract.Assert(s.rhss.Count > 0);
            // Create a hidden update statement using the out-parameter formals, resolve the RHS, and check that the RHS is good.
            List<Expression> formals = new List<Expression>();
            foreach (Formal f in cmc.Outs) {
              Expression produceLhs;
              if (stmt is ReturnStmt) {
                var ident = new IdentifierExpr(f.tok, f.Name);
                // resolve it here to avoid capture into more closely declared local variables
                Contract.Assert(f.Type != null);
                ident.Var = f;
                ident.PreType = Type2PreType(ident.Var.Type);
                produceLhs = ident;
              } else {
                var yieldIdent = new MemberSelectExpr(f.tok, new ImplicitThisExpr(f.tok), f.Name);
                ResolveExpression(yieldIdent, new Resolver.ResolveOpts(codeContext, true));
                produceLhs = yieldIdent;
              }
              formals.Add(produceLhs);
            }
            s.hiddenUpdate = new UpdateStmt(s.Tok, s.EndTok, formals, s.rhss, true);
            // resolving the update statement will check for return/yield statement specifics.
            ResolveStatement(s.hiddenUpdate, codeContext);
          }
        }

      } else if (stmt is ConcreteUpdateStatement concreteUpdateStatement) {
        ResolveConcreteUpdateStmt(concreteUpdateStatement, codeContext);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        // We have four cases.
        Contract.Assert(s.Update == null || s.Update is AssignSuchThatStmt || s.Update is UpdateStmt || s.Update is AssignOrReturnStmt);
        // 0.  There is no .Update.  This is easy, we will just resolve the locals.
        // 1.  The .Update is an AssignSuchThatStmt.  This is also straightforward:  first
        //     resolve the locals, which adds them to the scope, and then resolve the .Update.
        // 2.  The .Update is an UpdateStmt, which, resolved, means either a CallStmt or a bunch
        //     of simultaneous AssignStmt's.  Here, the right-hand sides should be resolved before
        //     the local variables have been added to the scope, but the left-hand sides should
        //     resolve to the newly introduced variables.
        // 3.  The .Update is a ":-" statement, for which resolution does two steps:
        //     First, desugar, then run the regular resolution on the desugared AST.
        // To accommodate these options, we first reach into the UpdateStmt, if any, to resolve
        // the left-hand sides of the UpdateStmt.  This will have the effect of shielding them
        // from a subsequent resolution (since expression resolution will do nothing if the .PreType
        // field is already assigned.
        // Alright, so it is:

        // Resolve the types of the locals
        foreach (var local in s.Locals) {
          int prevErrorCount = ErrorCount;
          resolver.ResolveType(local.Tok, local.OptionalType, codeContext, Resolver.ResolveTypeOptionEnum.InferTypeProxies, null);
          if (ErrorCount == prevErrorCount) {
            local.type = local.OptionalType;
          } else {
            local.type = new InferredTypeProxy();
          }
        }
        // Resolve the UpdateStmt or AssignOrReturnStmt, if any
        if (s.Update is UpdateStmt || s.Update is AssignOrReturnStmt) {
          var concreteUpdateStmt = (ConcreteUpdateStatement)s.Update;
          // resolve the LHS
          Contract.Assert(concreteUpdateStmt.Lhss.Count == s.Locals.Count);
          for (int i = 0; i < concreteUpdateStmt.Lhss.Count; i++) {
            var local = s.Locals[i];
            // the cast on the next line is justified, because that's how the parser creates the VarDeclStmt
            var lhs = (IdentifierExpr)concreteUpdateStmt.Lhss[i];
            Contract.Assert(lhs.PreType == null);  // not yet resolved
            lhs.Var = local;
            lhs.PreType = Type2PreType(local.Type);
          }
          if (concreteUpdateStmt is AssignOrReturnStmt assignOrReturnStmt) {
            ResolveAssignOrReturnStmt(assignOrReturnStmt, codeContext);
          } else {
            ResolveConcreteUpdateStmt(concreteUpdateStmt, codeContext);
          }
        }

        // Add the locals to the scope
        foreach (var local in s.Locals) {
          ScopePushAndReport(scope, local, "local-variable");
        }
        // With the new locals in scope, it's now time to resolve the attributes on all the locals
        foreach (var local in s.Locals) {
          ResolveAttributes(local, new Resolver.ResolveOpts(codeContext, true), false);
        }
        // Resolve the AssignSuchThatStmt, if any
        if (s.Update is AssignSuchThatStmt) {
          ResolveConcreteUpdateStmt(s.Update, codeContext);
        }
        // Check on "assumption" variables
        foreach (var local in s.Locals) {
          if (Attributes.Contains(local.Attributes, "assumption")) {
            if (currentMethod != null) {
              ConstrainSubtypeRelation(Type2PreType(Type.Bool), Type2PreType(local.type), local.Tok, "assumption variable must be of type 'bool'");
              if (!local.IsGhost) {
                ReportError(local.Tok, "assumption variable must be ghost");
              }
            } else {
              ReportError(local.Tok, "assumption variable can only be declared in a method");
            }
          }
        }

#if SOON
      } else if (stmt is VarDeclPattern) {
        VarDeclPattern s = (VarDeclPattern)stmt;
        foreach (var local in s.LocalVars) {
          int prevErrorCount = reporter.Count(ErrorLevel.Error);
          ResolveType(local.Tok, local.OptionalType, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
            local.type = local.OptionalType;
          } else {
            local.type = new InferredTypeProxy();
          }
        }
        ResolveExpression(s.RHS, new Resolver.ResolveOpts(codeContext, true));
        ResolveCasePattern(s.LHS, s.RHS.Type, codeContext);
        // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
        var c = 0;
        foreach (var bv in s.LHS.Vars) {
          ScopePushAndReport(scope, bv, "local_variable");
          c++;
        }
        if (c == 0) {
          // Every identifier-looking thing in the pattern resolved to a constructor; that is, this LHS is a constant literal
          ReportError(s.LHS.tok, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
        }
#endif

      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        int prevErrorCount = ErrorCount;
        ResolveExpression(s.Lhs, new Resolver.ResolveOpts(codeContext, true));  // allow ghosts for now, tightened up below
        bool lhsResolvedSuccessfully = ErrorCount == prevErrorCount;
        // check that LHS denotes a mutable variable or a field
        var lhs = s.Lhs.Resolved;
        if (lhs is IdentifierExpr) {
          IVariable var = ((IdentifierExpr)lhs).Var;
          if (var == null) {
            // the LHS didn't resolve correctly; some error would already have been reported
          } else {
            CheckIsLvalue(lhs, codeContext);

            if (var is LocalVariable localVar && currentMethod != null && Attributes.Contains(localVar.Attributes, "assumption")) {
              if ((s.Rhs as ExprRhs)?.Expr is BinaryExpr binaryExpr
                  && binaryExpr.Op == BinaryExpr.Opcode.And
                  && binaryExpr.E0.Resolved is IdentifierExpr e0idExpr
                  && e0idExpr.Var == localVar
                  && !currentMethod.AssignedAssumptionVariables.Contains(localVar)) {
                currentMethod.AssignedAssumptionVariables.Add(localVar);
              } else {
                ReportError(stmt,
                  $"there may be at most one assignment to an assumption variable, the RHS of which must match the expression \"{localVar.Name} && <boolean expression>\"");
              }
            }
          }
        } else if (lhs is MemberSelectExpr mseLhs) {
          if (mseLhs.Member != null) {  // otherwise, an error was reported above
            CheckIsLvalue(mseLhs, codeContext);
          }
        } else if (lhs is SeqSelectExpr sseLhs) {
          // LHS is fine, provided the "sequence" is really an array
          if (lhsResolvedSuccessfully) {
            CheckIsLvalue(sseLhs, codeContext);
          }
        } else {
          CheckIsLvalue(lhs, codeContext);
        }
        Type lhsType = s.Lhs.Type;
        if (s.Rhs is ExprRhs) {
          var rr = (ExprRhs)s.Rhs;
          ResolveExpression(rr.Expr, new Resolver.ResolveOpts(codeContext, true));
          AddAssignableConstraint(stmt.Tok, lhsType, rr.Expr.Type, "RHS (of type {1}) not assignable to LHS (of type {0})");
        } else if (s.Rhs is TypeRhs) {
          var rr = (TypeRhs)s.Rhs;
#if SOON
          Type t = ResolveTypeRhs(rr, stmt, codeContext);
          AddAssignableConstraint(stmt.Tok, lhsType, t, "type {1} is not assignable to LHS (of type {0})");
#endif
        } else if (s.Rhs is HavocRhs) {
          // nothing else to do
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
        }

#if SOON
      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        ResolveCallStmt(s, codeContext, null);
#endif

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        scope.PushMarker();
        ResolveBlockStatement(s, codeContext);
        scope.PopMarker();

#if SOON
      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        if (s.Guard != null) {
          ResolveExpression(s.Guard, new Resolver.ResolveOpts(codeContext, true));
          ConstrainTypeExprBool(s.Guard, "condition is expected to be of type bool, but is {0}");
        }

        scope.PushMarker();
        if (s.IsBindingGuard) {
          var exists = (ExistsExpr)s.Guard;
          foreach (var v in exists.BoundVars) {
            ScopePushAndReport(scope, v, "bound-variable");
          }
        }
        dominatingStatementLabels.PushMarker();
        ResolveBlockStatement(s.Thn, codeContext);
        dominatingStatementLabels.PopMarker();
        scope.PopMarker();

        if (s.Els != null) {
          dominatingStatementLabels.PushMarker();
          ResolveStatement(s.Els, codeContext);
          dominatingStatementLabels.PopMarker();
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        ResolveAlternatives(s.Alternatives, null, codeContext);

      } else if (stmt is OneBodyLoopStmt) {
        var s = (OneBodyLoopStmt)stmt;
        var fvs = new HashSet<IVariable>();
        var usesHeap = false;
        if (s is WhileStmt whileS && whileS.Guard != null) {
          ResolveExpression(whileS.Guard, new Resolver.ResolveOpts(codeContext, true));
          FreeVariablesUtil.ComputeFreeVariables(whileS.Guard, fvs, ref usesHeap);
          ConstrainTypeExprBool(whileS.Guard, "condition is expected to be of type bool, but is {0}");
        } else if (s is ForLoopStmt forS) {
          var loopIndex = forS.LoopIndex;
          int prevErrorCount = reporter.Count(ErrorLevel.Error);
          ResolveType(loopIndex.Tok, loopIndex.Type, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var err = new TypeConstraint.ErrorMsgWithToken(loopIndex.Tok, "index variable is expected to be of an integer type (got {0})", loopIndex.Type);
          ConstrainToIntegerType(loopIndex.Tok, loopIndex.Type, false, err);
          fvs.Add(loopIndex);

          ResolveExpression(forS.Start, new Resolver.ResolveOpts(codeContext, true));
          FreeVariablesUtil.ComputeFreeVariables(forS.Start, fvs, ref usesHeap);
          AddAssignableConstraint(forS.Start.tok, forS.LoopIndex.Type, forS.Start.Type, "lower bound (of type {1}) not assignable to index variable (of type {0})");
          if (forS.End != null) {
            ResolveExpression(forS.End, new Resolver.ResolveOpts(codeContext, true));
            FreeVariablesUtil.ComputeFreeVariables(forS.End, fvs, ref usesHeap);
            AddAssignableConstraint(forS.End.tok, forS.LoopIndex.Type, forS.End.Type, "upper bound (of type {1}) not assignable to index variable (of type {0})");
            if (forS.Decreases.Expressions.Count != 0) {
              ReportError(forS.Decreases.Expressions[0].tok,
                "a 'for' loop is allowed an explicit 'decreases' clause only if the end-expression is '*'");
            }
          } else if (forS.Decreases.Expressions.Count == 0 && !codeContext.AllowsNontermination) {
            // note, the following error message is also emitted elsewhere (if the loop bears a "decreases *")
            ReportError(forS.Tok,
              "a possibly infinite loop is allowed only if the enclosing method is declared (with 'decreases *') to be possibly non-terminating" +
              " (or you can add a 'decreases' clause to this 'for' loop if you want to prove that it does indeed terminate)");
          }

          // Create a new scope, add the local to the scope, and resolve the attributes
          scope.PushMarker();
          ScopePushAndReport(scope, loopIndex, "index-variable");
          ResolveAttributes(s, new Resolver.ResolveOpts(codeContext, true, false));
        }

        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, codeContext, fvs, ref usesHeap);

        if (s.Body != null) {
          loopStack.Add(s);  // push
          dominatingStatementLabels.PushMarker();
          ResolveStatement(s.Body, codeContext);
          dominatingStatementLabels.PopMarker();
          loopStack.RemoveAt(loopStack.Count - 1);  // pop
        } else {
          Contract.Assert(s.BodySurrogate == null);  // .BodySurrogate is set only once
          var loopFrame = new List<IVariable>();
          if (s is ForLoopStmt forLoopStmt) {
            loopFrame.Add(forLoopStmt.LoopIndex);
          }
          loopFrame.AddRange(fvs.Where(fv => fv.IsMutable));
          s.BodySurrogate = new WhileStmt.LoopBodySurrogate(loopFrame, usesHeap);
          var text = Util.Comma(s.BodySurrogate.LocalLoopTargets, fv => fv.Name);
          if (s.BodySurrogate.UsesHeap) {
            text += text.Length == 0 ? "$Heap" : ", $Heap";
          }
          text = string.Format("note, this loop has no body{0}", text.Length == 0 ? "" : " (loop frame: " + text + ")");
          reporter.Warning(MessageSource.Resolver, s.Tok, text);
        }

        if (s is ForLoopStmt) {
          scope.PopMarker();
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        ResolveAlternatives(s.Alternatives, s, codeContext);
        var usesHeapDontCare = false;
        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, codeContext, null, ref usesHeapDontCare);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;

        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in s.BoundVars) {
          ScopePushAndReport(scope, v, "local-variable");
          ResolveType(v.tok, v.Type, codeContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
        ResolveExpression(s.Range, new Resolver.ResolveOpts(codeContext, true));
        ConstrainTypeExprBool(s.Range, "range restriction in forall statement must be of type bool (instead got {0})");
        foreach (var ens in s.Ens) {
          ResolveExpression(ens.E, new Resolver.ResolveOpts(codeContext, true));
          ConstrainTypeExprBool(ens.E, "ensures condition is expected to be of type bool, but is {0}");
        }
        // Since the range and postconditions are more likely to infer the types of the bound variables, resolve them
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(s, new Resolver.ResolveOpts(codeContext, true), false);

        if (s.Body != null) {
          // clear the labels for the duration of checking the body, because break statements are not allowed to leave a forall statement
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          ResolveStatement(s.Body, codeContext);
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;
        } else {
          reporter.Warning(MessageSource.Resolver, s.Tok, "note, this forall statement has no body");
        }
        scope.PopMarker();

        if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
          // determine the Kind and run some additional checks on the body
          if (s.Ens.Count != 0) {
            // The only supported kind with ensures clauses is Proof.
            s.Kind = ForallStmt.BodyKind.Proof;
          } else {
            // There are three special cases:
            // * Assign, which is the only kind of the forall statement that allows a heap update.
            // * Call, which is a single call statement with no side effects or output parameters.
            // * A single calc statement, which is a special case of Proof where the postcondition can be inferred.
            // The effect of Assign and the postcondition of Call will be seen outside the forall
            // statement.
            Statement s0 = s.S0;
            if (s0 is AssignStmt) {
              s.Kind = ForallStmt.BodyKind.Assign;

              var rhs = ((AssignStmt)s0).Rhs;
              if (rhs is TypeRhs) {
                ReportError(rhs.Tok, "new allocation not supported in aggregate assignments");
              }

            } else if (s0 is CallStmt) {
              s.Kind = ForallStmt.BodyKind.Call;
              var call = (CallStmt)s.S0;
              var method = call.Method;
              // if the called method is not in the same module as the ForallCall stmt
              // don't convert it to ForallExpression since the inlined called method's
              // ensure clause might not be resolved correctly(test\dafny3\GenericSort.dfy)
              if (method.EnclosingClass.EnclosingModuleDefinition != codeContext.EnclosingModule) {
                s.CanConvert = false;
              }
              // Additional information (namely, the postcondition of the call) will be reported later. But it cannot be
              // done yet, because the specification of the callee may not have been resolved yet.
            } else if (s0 is CalcStmt) {
              s.Kind = ForallStmt.BodyKind.Proof;
              // add the conclusion of the calc as a free postcondition
              var result = ((CalcStmt)s0).Result;
              s.Ens.Add(new AttributedExpression(result));
              reporter.Info(MessageSource.Resolver, s.Tok, "ensures " + Printer.ExprToString(result));
            } else {
              s.Kind = ForallStmt.BodyKind.Proof;
              if (s.Body is BlockStmt && ((BlockStmt)s.Body).Body.Count == 0) {
                // an empty statement, so don't produce any warning
              } else {
                reporter.Warning(MessageSource.Resolver, s.Tok, "the conclusion of the body of this forall statement will not be known outside the forall statement; consider using an 'ensures' clause");
              }
            }
          }

          if (s.ForallExpressions != null) {
            foreach (Expression expr in s.ForallExpressions) {
              ResolveExpression(expr, new Resolver.ResolveOpts(codeContext, true));
            }
          }
        }

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        ResolveAttributes(s.Mod, new Resolver.ResolveOpts(codeContext, true), false);
        foreach (FrameExpression fe in s.Mod.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, codeContext);
        }
        if (s.Body != null) {
          ResolveBlockStatement(s.Body, codeContext);
        }

      } else if (stmt is CalcStmt) {
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        CalcStmt s = (CalcStmt)stmt;
        // figure out s.Op
        Contract.Assert(s.Op == null);  // it hasn't been set yet
        if (s.UserSuppliedOp != null) {
          s.Op = s.UserSuppliedOp;
        } else {
          // Usually, we'd use == as the default main operator.  However, if the calculation
          // begins or ends with a boolean literal, then we can do better by selecting ==>
          // or <==.  Also, if the calculation begins or ends with an empty set, then we can
          // do better by selecting <= or >=.
          if (s.Lines.Count == 0) {
            s.Op = CalcStmt.DefaultOp;
          } else {
            bool b;
            if (Expression.IsBoolLiteral(s.Lines.First(), out b)) {
              s.Op = new CalcStmt.BinaryCalcOp(b ? BinaryExpr.Opcode.Imp : BinaryExpr.Opcode.Exp);
            } else if (Expression.IsBoolLiteral(s.Lines.Last(), out b)) {
              s.Op = new CalcStmt.BinaryCalcOp(b ? BinaryExpr.Opcode.Exp : BinaryExpr.Opcode.Imp);
            } else if (Expression.IsEmptySetOrMultiset(s.Lines.First())) {
              s.Op = new CalcStmt.BinaryCalcOp(BinaryExpr.Opcode.Ge);
            } else if (Expression.IsEmptySetOrMultiset(s.Lines.Last())) {
              s.Op = new CalcStmt.BinaryCalcOp(BinaryExpr.Opcode.Le);
            } else {
              s.Op = CalcStmt.DefaultOp;
            }
          }
          reporter.Info(MessageSource.Resolver, s.Tok, s.Op.ToString());
        }

        if (s.Lines.Count > 0) {
          Type lineType = new InferredTypeProxy();
          var e0 = s.Lines.First();
          ResolveExpression(e0, new Resolver.ResolveOpts(codeContext, true));
          var err = new TypeConstraint.ErrorMsgWithToken(e0.tok, "all lines in a calculation must have the same type (got {0} after {1})", e0.Type, lineType);
          ConstrainSubtypeRelation(lineType, e0.Type, err);
          for (int i = 1; i < s.Lines.Count; i++) {
            var e1 = s.Lines[i];
            ResolveExpression(e1, new Resolver.ResolveOpts(codeContext, true));
            // reuse the error object if we're on the dummy line; this prevents a duplicate error message
            if (i < s.Lines.Count - 1) {
              err = new TypeConstraint.ErrorMsgWithToken(e1.tok, "all lines in a calculation must have the same type (got {0} after {1})", e1.Type, lineType);
            }
            ConstrainSubtypeRelation(lineType, e1.Type, err);
            var step = (s.StepOps[i - 1] ?? s.Op).StepExpr(e0, e1); // Use custom line operator
            ResolveExpression(step, new Resolver.ResolveOpts(codeContext, true));
            s.Steps.Add(step);
            e0 = e1;
          }

          // clear the labels for the duration of checking the hints, because break statements are not allowed to leave a forall statement
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          foreach (var h in s.Hints) {
            foreach (var oneHint in h.Body) {
              dominatingStatementLabels.PushMarker();
              ResolveStatement(oneHint, codeContext);
              dominatingStatementLabels.PopMarker();
            }
          }
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;

        }
        if (prevErrorCount == reporter.Count(ErrorLevel.Error) && s.Lines.Count > 0) {
          // do not build Result from the lines if there were errors, as it might be ill-typed and produce unnecessary resolution errors
          var resultOp = s.StepOps.Aggregate(s.Op, (op0, op1) => op1 == null ? op0 : op0.ResultOp(op1));
          s.Result = resultOp.StepExpr(s.Lines.First(), s.Lines.Last());
        } else {
          s.Result = CalcStmt.DefaultOp.StepExpr(Expression.CreateIntLiteral(s.Tok, 0), Expression.CreateIntLiteral(s.Tok, 0));
        }
        ResolveExpression(s.Result, new Resolver.ResolveOpts(codeContext, true));
        Contract.Assert(s.Result != null);
        Contract.Assert(prevErrorCount != reporter.Count(ErrorLevel.Error) || s.Steps.Count == s.Hints.Count);

      } else if (stmt is MatchStmt) {
        ResolveMatchStmt((MatchStmt)stmt, codeContext);

      } else if (stmt is NestedMatchStmt) {
        var s = (NestedMatchStmt)stmt;
        var opts = new Resolver.ResolveOpts(codeContext, false);
        ResolveNestedMatchStmt(s, opts);
      } else if (stmt is SkeletonStatement) {
        var s = (SkeletonStatement)stmt;
        ReportError(s.Tok, "skeleton statements are allowed only in refining methods");
        // nevertheless, resolve the underlying statement; hey, why not
        if (s.S != null) {
          ResolveStatement(s.S, codeContext);
        }
#endif
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private void ResolveConcreteUpdateStmt(ConcreteUpdateStatement s, ICodeContext codeContext) {
      Contract.Requires(s != null);
      Contract.Requires(codeContext != null);
#if SOON
      // First, resolve all LHS's and expression-looking RHS's.
      int errorCountBeforeCheckingLhs = reporter.Count(ErrorLevel.Error);

      var lhsNameSet = new HashSet<string>();  // used to check for duplicate identifiers on the left (full duplication checking for references and the like is done during verification)
      foreach (var lhs in s.Lhss) {
        var ec = reporter.Count(ErrorLevel.Error);
        ResolveExpression(lhs, new ResolveOpts(codeContext, true));
        if (ec == reporter.Count(ErrorLevel.Error)) {
          if (lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne) {
            reporter.Error(MessageSource.Resolver, lhs, "cannot assign to a range of array elements (try the 'forall' statement)");
          }
        }
      }

      // Resolve RHSs
      if (s is AssignSuchThatStmt) {
        ResolveAssignSuchThatStmt((AssignSuchThatStmt)s, codeContext);
      } else if (s is UpdateStmt) {
        ResolveUpdateStmt((UpdateStmt)s, codeContext, errorCountBeforeCheckingLhs);
      } else if (s is AssignOrReturnStmt) {
        ResolveAssignOrReturnStmt((AssignOrReturnStmt)s, codeContext);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
      ResolveAttributes(s, new ResolveOpts(codeContext, true)); // TODO: hasn't this already been done, at the top of ResolveStatement?
#endif
    }

    /// <summary>
    /// Desugars "y, ... :- MethodOrExpression" into
    /// var temp;
    /// temp, ... := MethodOrExpression;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    /// y := temp.Extract();
    ///
    /// If the type of MethodExpression does not have an Extract, then the desugaring is
    /// var temp;
    /// temp, y, ... := MethodOrExpression;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    ///
    /// If there are multiple RHSs then "y, ... :- Expression, ..." becomes
    /// var temp;
    /// temp, ... := Expression, ...;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    /// y := temp.Extract();
    /// OR
    /// var temp;
    /// temp, y, ... := Expression, ...;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    ///
    /// and "y, ... :- expect MethodOrExpression, ..." into
    /// var temp, [y, ] ... := MethodOrExpression, ...;
    /// expect !temp.IsFailure(), temp.PropagateFailure();
    /// [y := temp.Extract();]
    ///
    /// and saves the result into s.ResolvedStatements.
    /// This is also known as the "elephant operator"
    /// </summary>
    private void ResolveAssignOrReturnStmt(AssignOrReturnStmt s, ICodeContext codeContext) {
#if SOON
      // TODO Do I have any responsibilities regarding the use of codeContext? Is it mutable?

      // We need to figure out whether we are using a status type that has Extract or not,
      // as that determines how the AssignOrReturnStmt is desugared. Thus if the Rhs is a
      // method call we need to know which one (to inspect its first output); if RHs is a
      // list of expressions, we need to know the type of the first one. For all of this we have
      // to do some partial type resolution.

      bool expectExtract = s.Lhss.Count != 0; // default value if we cannot determine and inspect the type
      Type firstType = null;
      Method call = null;
      if (s.Rhss != null && s.Rhss.Count != 0) {
        ResolveExpression(s.Rhs, new ResolveOpts(codeContext, true));
        firstType = s.Rhs.Type;
      } else if (s.Rhs is ApplySuffix asx) {
        ResolveApplySuffix(asx, new ResolveOpts(codeContext, true), true);
        call = (asx.Lhs.Resolved as MemberSelectExpr)?.Member as Method;
        if (call != null) {
          // We're looking at a method call
          var typeMap = (asx.Lhs.Resolved as MemberSelectExpr)?.TypeArgumentSubstitutionsWithParents();
          if (call.Outs.Count != 0) {
            firstType = SubstType(call.Outs[0].Type, typeMap);
          } else {
            reporter.Error(MessageSource.Resolver, s.Rhs.tok, "Expected {0} to have a Success/Failure output value, but the method returns nothing.", call.Name);
          }
        } else {
          // We're looking at a call to a function. Treat it like any other expression.
          firstType = asx.Type;
        }
      } else {
        ResolveExpression(s.Rhs, new ResolveOpts(codeContext, true));
        firstType = s.Rhs.Type;
      }

      if ((codeContext as Method).Outs.Count == 0 && s.KeywordToken == null) {
        reporter.Error(MessageSource.Resolver, s.Tok, "A method containing a :- statement must have an out-parameter ({0})",
          (codeContext as Method).Name);
        return;
      }
      if (firstType != null) {
        firstType = PartiallyResolveTypeForMemberSelection(s.Rhs.tok, firstType);
        if (firstType.AsTopLevelTypeWithMembers != null) {
          if (firstType.AsTopLevelTypeWithMembers.Members.Find(x => x.Name == "IsFailure") == null) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "member IsFailure does not exist in {0}, in :- statement", firstType);
            return;
          }
          expectExtract = firstType.AsTopLevelTypeWithMembers.Members.Find(x => x.Name == "Extract") != null;
          if (expectExtract && call == null && s.Lhss.Count != 1 + s.Rhss.Count) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "number of lhs ({0}) must match number of rhs ({1}) for a rhs type ({2}) with member Extract",
              s.Lhss.Count, 1 + s.Rhss.Count, firstType);
            return;
          } else if (expectExtract && call != null && s.Lhss.Count != call.Outs.Count) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "wrong number of method result arguments (got {0}, expected {1}) for a rhs type ({2}) with member Extract",
              s.Lhss.Count, call.Outs.Count, firstType);
            return;

          } else if (!expectExtract && call == null && s.Lhss.Count != s.Rhss.Count) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "number of lhs ({0}) must be one less than number of rhs ({1}) for a rhs type ({2}) without member Extract", s.Lhss.Count, 1 + s.Rhss.Count, firstType);
            return;

          } else if (!expectExtract && call != null && s.Lhss.Count != call.Outs.Count - 1) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "wrong number of method result arguments (got {0}, expected {1}) for a rhs type ({2}) without member Extract", s.Lhss.Count, call.Outs.Count - 1, firstType);
            return;
          }
        } else {
          reporter.Error(MessageSource.Resolver, s.Tok,
            $"The type of the first expression to the right of ':-' could not be determined to be a failure type (got '{firstType}')");
          return;
        }
      } else {
        reporter.Error(MessageSource.Resolver, s.Tok,
          "Internal Error: Unknown failure type in :- statement");
        return;
      }

      Expression lhsExtract = null;
      if (expectExtract) {
        Method caller = codeContext as Method;
        if (caller != null && caller.Outs.Count == 0 && s.KeywordToken == null) {
          reporter.Error(MessageSource.Resolver, s.Rhs.tok, "Expected {0} to have a Success/Failure output value",
            caller.Name);
          return;
        }

        lhsExtract = s.Lhss[0];
        var lhsResolved = s.Lhss[0].Resolved;
        // Make a new unresolved expression
        if (lhsResolved is MemberSelectExpr lexr) {
          Expression id = Expression.AsThis(lexr.Obj) != null ? lexr.Obj : makeTemp("recv", s, codeContext, lexr.Obj);
          var lex = lhsExtract as ExprDotName; // might be just a NameSegment
          lhsExtract = new ExprDotName(lexr.tok, id, lexr.MemberName, lex == null ? null : lex.OptTypeArguments);
        } else if (lhsResolved is SeqSelectExpr lseq) {
          if (!lseq.SelectOne || lseq.E0 == null) {
            reporter.Error(MessageSource.Resolver, s.Tok,
              "Element ranges not allowed as l-values");
            return;
          }
          Expression id = makeTemp("recv", s, codeContext, lseq.Seq);
          Expression id0 = id0 = makeTemp("idx", s, codeContext, lseq.E0);
          lhsExtract = new SeqSelectExpr(lseq.tok, lseq.SelectOne, id, id0, null);
          lhsExtract.Type = lseq.Type;
        } else if (lhsResolved is MultiSelectExpr lmulti) {
          Expression id = makeTemp("recv", s, codeContext, lmulti.Array);
          var idxs = new List<Expression>();
          foreach (var i in lmulti.Indices) {
            Expression idx = makeTemp("idx", s, codeContext, i);
            idxs.Add(idx);
          }
          lhsExtract = new MultiSelectExpr(lmulti.tok, id, idxs);
          lhsExtract.Type = lmulti.Type;
        } else if (lhsResolved is IdentifierExpr) {
          // do nothing
        } else {
          Contract.Assert(false, "Internal error: unexpected option in ResolveAssignOrReturnStmt");
        }
      }
      var temp = FreshTempVarName("valueOrError", codeContext);
      var lhss = new List<LocalVariable>() { new LocalVariable(s.Tok, s.Tok, temp, new InferredTypeProxy(), false) };
      // "var temp ;"
      s.ResolvedStatements.Add(new VarDeclStmt(s.Tok, s.Tok, lhss, null));
      var lhss2 = new List<Expression>() { new IdentifierExpr(s.Tok, temp) };
      for (int k = (expectExtract ? 1 : 0); k < s.Lhss.Count; ++k) {
        lhss2.Add(s.Lhss[k]);
      }
      List<AssignmentRhs> rhss2 = new List<AssignmentRhs>() { new ExprRhs(s.Rhs) };
      if (s.Rhss != null) {
        s.Rhss.ForEach(e => rhss2.Add(e));
      }
      if (s.Rhss != null && s.Rhss.Count > 0) {
        if (lhss2.Count != rhss2.Count) {
          reporter.Error(MessageSource.Resolver, s.Tok,
            "Mismatch in expected number of LHSs and RHSs");
          if (lhss2.Count < rhss2.Count) {
            rhss2.RemoveRange(lhss2.Count, rhss2.Count - lhss2.Count);
          } else {
            lhss2.RemoveRange(rhss2.Count, lhss2.Count - rhss2.Count);
          }
        }
      }
      // " temp, ... := MethodOrExpression, ...;"
      UpdateStmt up = new UpdateStmt(s.Tok, s.Tok, lhss2, rhss2);
      if (expectExtract) {
        up.OriginalInitialLhs = s.Lhss.Count == 0 ? null : s.Lhss[0];
      }
      s.ResolvedStatements.Add(up);

      if (s.KeywordToken != null) {
        var notFailureExpr = new UnaryOpExpr(s.Tok, UnaryOpExpr.Opcode.Not, VarDotMethod(s.Tok, temp, "IsFailure"));
        Statement ss = null;
        if (s.KeywordToken.val == "expect") {
          // "expect !temp.IsFailure(), temp"
          ss = new ExpectStmt(s.Tok, s.Tok, notFailureExpr, new IdentifierExpr(s.Tok, temp), null);
        } else if (s.KeywordToken.val == "assume") {
          ss = new AssumeStmt(s.Tok, s.Tok, notFailureExpr, null);
        } else if (s.KeywordToken.val == "assert") {
          ss = new AssertStmt(s.Tok, s.Tok, notFailureExpr, null, null, null);
        } else {
          Contract.Assert(false, $"Invalid token in :- statement: {s.KeywordToken.val}");
        }
        s.ResolvedStatements.Add(ss);
      } else {
        var enclosingOutParameter = ((Method)codeContext).Outs[0];
        var ident = new IdentifierExpr(s.Tok, enclosingOutParameter.Name);
        // resolve it here to avoid capture into more closely declared local variables
        Contract.Assert(enclosingOutParameter.Type != null);  // this confirms our belief that the out-parameter has already been resolved
        ident.Var = enclosingOutParameter;
        ident.Type = ident.Var.Type;

        s.ResolvedStatements.Add(
          // "if temp.IsFailure()"
          new IfStmt(s.Tok, s.Tok, false, VarDotMethod(s.Tok, temp, "IsFailure"),
            // THEN: { out := temp.PropagateFailure(); return; }
            new BlockStmt(s.Tok, s.Tok, new List<Statement>() {
              new UpdateStmt(s.Tok, s.Tok,
                new List<Expression>() { ident },
                new List<AssignmentRhs>() {new ExprRhs(VarDotMethod(s.Tok, temp, "PropagateFailure"))}
                ),
              new ReturnStmt(s.Tok, s.Tok, null),
            }),
            // ELSE: no else block
            null
          ));
      }

      if (expectExtract) {
        // "y := temp.Extract();"
        var lhs = s.Lhss[0];
        s.ResolvedStatements.Add(
          new UpdateStmt(s.Tok, s.Tok,
            new List<Expression>() { lhsExtract },
            new List<AssignmentRhs>() { new ExprRhs(VarDotMethod(s.Tok, temp, "Extract")) }
          ));
        // The following check is not necessary, because the ghost mismatch is caught later.
        // However the error message here is much clearer.
        var m = ResolveMember(s.Tok, firstType, "Extract", out _);
        if (m != null && m.IsGhost && !AssignStmt.LhsIsToGhostOrAutoGhost(lhs)) {
          reporter.Error(MessageSource.Resolver, lhs.tok,
            "The Extract member may not be ghost unless the initial LHS is ghost");
        }
      }

      s.ResolvedStatements.ForEach(a => ResolveStatement(a, codeContext));
      EnsureSupportsErrorHandling(s.Tok, firstType, expectExtract, s.KeywordToken != null);
#endif
    }

    /// <summary>
    /// Checks if lhs, which is expected to be a successfully resolved expression, denotes something
    /// that can be assigned to.  In particular, this means that lhs denotes a mutable variable, field,
    /// or array element.  If a violation is detected, an error is reported.
    /// </summary>
    void CheckIsLvalue(Expression lhs, ICodeContext codeContext) {
      Contract.Requires(lhs != null);
      Contract.Requires(codeContext != null);
      if (lhs is IdentifierExpr) {
        var ll = (IdentifierExpr)lhs;
        if (!ll.Var.IsMutable) {
          ReportError(lhs, "LHS of assignment must denote a mutable variable");
        }
      } else if (lhs is MemberSelectExpr) {
        var ll = (MemberSelectExpr)lhs;
        var field = ll.Member as Field;
        if (field == null || !field.IsUserMutable) {
          var cf = field as ConstantField;
          if (inBodyInitContext && cf != null && !cf.IsStatic && cf.Rhs == null) {
            if (Expression.AsThis(ll.Obj) != null) {
              // it's cool; this field can be assigned to here
            } else {
              ReportError(lhs, "LHS of assignment must denote a mutable field of 'this'");
            }
          } else {
            ReportError(lhs, "LHS of assignment must denote a mutable field");
          }
        }
      } else if (lhs is SeqSelectExpr) {
        var ll = (SeqSelectExpr)lhs;
        ConstrainSubtypeRelation(resolver.ResolvedArrayType(ll.Seq.tok, 1, new InferredTypeProxy(), codeContext, true),
          ll.Seq.Type, ll.Seq,
          "LHS of array assignment must denote an array element (found {0})", ll.Seq.Type);
        if (!ll.SelectOne) {
          ReportError(ll.Seq, "cannot assign to a range of array elements (try the 'forall' statement)");
        }
      } else if (lhs is MultiSelectExpr) {
        // nothing to check; this can only denote an array element
      } else {
        ReportError(lhs, "LHS of assignment must denote a mutable variable or field");
      }
    }
  }
}
