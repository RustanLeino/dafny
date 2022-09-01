#define DEBUG_IMPROVEMENT
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
using JetBrains.Annotations;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  /// <summary>
  /// TypeImprovementValue is to have subclass implementations in each TypeImprovement system.
  /// </summary>
  public abstract class TypeImprovementValue {
    public static readonly TypeImprovementValue Top = null;
    [CanBeNull] public readonly List<TypeImprovementValue> Arguments; // null is a synonymous with .Count == 0 (which is a common case)

    public string ArgumentsToString() {
      if (Arguments == null) {
        return "";
      } else {
        return $"<{Arguments.Comma(arg => arg.PrintString())}>";
      }
    }

    public TypeImprovementValue([CanBeNull] List<TypeImprovementValue> arguments = null) {
      Arguments = arguments;
    }
  }

  public static class TypeImprovementValueExtensionMethods {
    public static string PrintString(this TypeImprovementValue th) {
      return th == null ? "\\top" : th.ToString();
    }
  }

  public abstract record TypeImprovement {
    public static readonly TypeImprovement Top = new TypeImprovementConstant(TypeImprovementValue.Top);

    [CanBeNull]
    public abstract TypeImprovementValue Evaluate();
  }

  /// <summary>
  /// A "Value" of "null" indicates the constant \top.
  /// </summary>
  public record TypeImprovementConstant([CanBeNull] TypeImprovementValue Value) : TypeImprovement {
    public override string ToString() => $"Const({Value.PrintString()})";

    public override TypeImprovementValue Evaluate() => Value;
  }

  public record TypeImprovementVariable(string Name) : TypeImprovement {
    /// <summary>
    /// "CurrentValue == Bottom" indicates \bottom.
    /// "CurrentValue == TypeImprovement.Top" indicates \top.
    /// </summary>
    public TypeImprovementValue CurrentValue = Bottom;

    public bool IsBottom => CurrentValue == Bottom;

    private class BottomValue : TypeImprovementValue {
      public override string ToString() => "\\bottom";
    }

    private static readonly BottomValue Bottom = new BottomValue();

    public bool Update(TypeImprovementValue tiValue) {
      if (CurrentValue == Bottom || CurrentValue != tiValue) {
#if DEBUG_IMPROVEMENT
        Console.WriteLine($"  --updating {Name} := {tiValue.PrintString()}");
#endif
        CurrentValue = tiValue;
        return true; // value was updated
      }
      return false; // no change to the value
    }

    public override string ToString() {
      var value = CurrentValue.PrintString();
      return $"Var(\"{Name}\", current := {value})";
    }

    public override TypeImprovementValue Evaluate() => CurrentValue;
  }

  public abstract class TypeImprover : ResolverPass {
    public TypeImprover(Resolver resolver)
      : base(resolver) {
    }

    public void Improve(List<TopLevelDecl> declarations) {
      Contract.Requires(declarations != null);

      foreach (TopLevelDecl d in declarations) {
        if (d is IteratorDecl) {
#if SOON
          var iter = (IteratorDecl)d;
          var prevErrCnt = ErrorCount;
          foreach (var formal in iter.Ins) {
            if (formal.DefaultValue != null) {
              CheckExpression(formal.DefaultValue, iter);
            }
          }
          iter.Members.Iter(CheckMember);
          if (prevErrCnt == ErrorCount) {
            iter.SubExpressions.Iter(e => CheckExpression(e, iter));
          }
          CheckParameterDefaultValues(iter.Ins, iter);
          if (iter.Body != null) {
            CheckExpressions(iter.Body, iter);
            if (prevErrCnt == ErrorCount) {
              CheckExpressions(iter.Body, iter);
            }
          }

        } else if (d is SubsetTypeDecl) {
          var dd = (SubsetTypeDecl)d;
#if SOON
          if (!DetectUnderspecificationVisitor.IsDetermined(dd.Rhs)) {
            ReportError(dd, "subset type's base type is not fully determined; add an explicit type for '{0}'", dd.Var.Name);
          }
#endif
          CheckExpression(dd.Constraint, new CodeContextWrapper(dd, true));
          if (dd.Witness != null) {
            CheckExpression(dd.Witness, new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost));
          }

        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          if (dd.Var != null) {
            if (!DetectUnderspecificationVisitor.IsDetermined(dd.BasePreType)) {
              ReportError(dd, "newtype's base type is not fully determined; add an explicit type for '{0}'", dd.Var.Name);
            }
            CheckExpression(dd.Constraint, new CodeContextWrapper(dd, true));
            if (dd.Witness != null) {
              CheckExpression(dd.Witness, new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost));
            }
          }
#if SOON
          resolver.FigureOutNativeType(dd);
#endif
          CheckMembers(dd);

        } else if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          foreach (var ctor in dd.Ctors) {
            foreach (var formal in ctor.Formals) {
              if (formal.DefaultValue != null) {
                CheckExpression(formal.DefaultValue, dd);
              }
            }
          }
          foreach (var member in resolver.classMembers[dd].Values) {
            var dtor = member as DatatypeDestructor;
            if (dtor != null) {
              var rolemodel = dtor.CorrespondingFormals[0];
              for (int i = 1; i < dtor.CorrespondingFormals.Count; i++) {
                var other = dtor.CorrespondingFormals[i];
                if (!Type.Equal_Improved(rolemodel.Type, other.Type)) {
                  ReportError(other.tok,
                    "shared destructors must have the same type, but '{0}' has type '{1}' in constructor '{2}' and type '{3}' in constructor '{4}'",
                    rolemodel.Name, rolemodel.Type, dtor.EnclosingCtors[0].Name, other.Type, dtor.EnclosingCtors[i].Name);
                } else if (rolemodel.IsGhost != other.IsGhost) {
                  ReportError(other.tok,
                    "shared destructors must agree on whether or not they are ghost, but '{0}' is {1} in constructor '{2}' and {3} in constructor '{4}'",
                    rolemodel.Name,
                    rolemodel.IsGhost ? "ghost" : "non-ghost", dtor.EnclosingCtors[0].Name,
                    other.IsGhost ? "ghost" : "non-ghost", dtor.EnclosingCtors[i].Name);
                }
              }
            }
          }
          foreach (var ctor in dd.Ctors) {
            CheckParameterDefaultValues(ctor.Formals, dd);
          }
          CheckMembers(dd);

#endif
        } else if (d is TopLevelDeclWithMembers md) {
          ImproveMembers(md);
        }
      }
    }

    void ImproveMembers(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);
      cl.Members.Iter(ImproveMember);
    }

    void ImproveMember(MemberDecl member) {
      if (member is ConstantField cfield && cfield.Rhs != null) {
        VisitExpression(cfield.Rhs);
        var tiVar = new TypeImprovementVariable(cfield.Name);
        cfield.TypeImprovement = tiVar;
        AddConstraint(tiVar, cfield.Rhs.TypeImprovement);

      } else if (member is Field field) {
        field.TypeImprovement = new TypeImprovementConstant(FromUserProvidedType(field.Type));

      } else if (member is Method method) {
        foreach (var formal in method.Ins) {
          formal.TypeImprovement = new TypeImprovementConstant(FromUserProvidedType(formal.Type));
          if (formal.DefaultValue != null) {
            VisitExpression(formal.DefaultValue);
          }
        }
        foreach (var formal in method.Outs) {
          formal.TypeImprovement = new TypeImprovementConstant(FromUserProvidedType(formal.Type));
        }
        method.Req.Iter(VisitAttributedExpression);
        VisitSpecFrameExpression(method.Mod);
        method.Ens.Iter(VisitAttributedExpression);
        VisitSpecExpression(method.Decreases);
        if (method.Body != null) {
          VisitStatement(method.Body);
        }

      } else if (member is Function) {
        var f = (Function)member;
        foreach (var formal in f.Formals) {
          formal.TypeImprovement = new TypeImprovementConstant(FromUserProvidedType(formal.Type));
          if (formal.DefaultValue != null) {
            VisitExpression(formal.DefaultValue);
          }
        }
        var errorCount = ErrorCount;
        f.Req.Iter(VisitAttributedExpression);
        f.Ens.Iter(VisitAttributedExpression);
        f.Reads.Iter(fe => VisitExpression(fe.E));
        VisitSpecExpression(f.Decreases);
        if (f.Body != null) {
          VisitExpression(f.Body);
        }
        if (errorCount == ErrorCount) {
          if (f is ExtremePredicate cop) {
            ImproveMember(cop.PrefixPredicate);
          } else if (f.ByMethodDecl != null) {
            ImproveMember(f.ByMethodDecl);
          }
        }
      }
    }

    [CanBeNull] public abstract TypeImprovementValue FromUserProvidedType(Type type);

    [CanBeNull] public abstract TypeImprovementValue Join(TypeImprovementValue a, TypeImprovementValue b);

    void VisitAttributes(Attributes attrs) {
      for (; attrs != null; attrs = attrs.Prev) {
        attrs.Args.Iter(VisitExpression);
      }
    }

    void VisitAttributedExpression(AttributedExpression aexpr) {
      VisitAttributes(aexpr.Attributes);
      VisitExpression(aexpr.E);
    }

    void VisitSpecExpression(Specification<Expression> specExpression) {
      VisitAttributes(specExpression.Attributes);
      specExpression.Expressions.Iter(VisitExpression);
    }

    void VisitSpecFrameExpression(Specification<FrameExpression> specFrameExpression) {
      VisitAttributes(specFrameExpression.Attributes);
      specFrameExpression.Expressions.Iter(fe => VisitExpression(fe.E));
    }

    void VisitExpression(Expression expr) {
      foreach (var e in expr.SubExpressions) {
        VisitExpression(e);
      }

      if (expr is IdentifierExpr idExpr) {
        if (idExpr.Var is LocalVariable local) {
          Contract.Assert(local.TypeImprovement != null);
          expr.TypeImprovement = local.TypeImprovement;
          return;
        } else if (idExpr.Var is Formal formal) {
          expr.TypeImprovement = new TypeImprovementConstant(FromUserProvidedType(formal.Type));
          return;
        }
      } else if (expr is ConcreteSyntaxExpression concreteSyntaxExpression) {
        concreteSyntaxExpression.TypeImprovement = concreteSyntaxExpression.ResolvedExpression.TypeImprovement;
        return;
      }

      // If nothing else, use \top.
      expr.TypeImprovement = TypeImprovement.Top;
    }

    void VisitStatement(Statement stmt) {
      foreach (var expr in stmt.SubExpressions) {
        VisitExpression(expr);
      }

      if (stmt is VarDeclStmt varDeclStmt) {
        foreach (var local in varDeclStmt.Locals) {
          Contract.Assert(local.TypeImprovement == null);
          var declaredImprovement = FromUserProvidedType(local.OptionalType);
          if (declaredImprovement != null) {
            local.TypeImprovement = new TypeImprovementConstant(declaredImprovement);
          } else {
            local.TypeImprovement = new TypeImprovementVariable(local.Name);
          }
        }
      } else if (stmt is AssignStmt assignStmt) {
        if (assignStmt.Lhs is IdentifierExpr idExpr && idExpr.Var is IVariable local && local.TypeImprovement is TypeImprovementVariable tiVar) {
          if (assignStmt.Rhs is ExprRhs exprRhs) {
            AddConstraint(tiVar, exprRhs.Expr.TypeImprovement);
          }
        }
      }

      foreach (var s in stmt.SubStatements) {
        VisitStatement(s);
      }
    }

    private List<(TypeImprovementVariable, TypeImprovement)> constraints = new();

    public void PrintConstraints(string header) {
#if DEBUG_IMPROVEMENT
      Console.WriteLine($"----------- {header} -------------");
      foreach (var (a, b) in constraints) {
        Console.WriteLine($"    {a.Name} <- {b}");
      }
#endif
    }

    void AddConstraint(TypeImprovementVariable a, TypeImprovement b) {
      constraints.Add((a, b));
    }

    public void SolveConstraints() {
      bool anyChange;

      do {
        anyChange = false;
        foreach (var (a, b) in constraints) {
          if (a is TypeImprovementVariable tiVar) {
            var bValue = b.Evaluate();
            if (tiVar.IsBottom || bValue == TypeImprovementValue.Top) {
              anyChange = tiVar.Update(bValue) || anyChange;
            } else if (tiVar.CurrentValue == TypeImprovementValue.Top) {
            } else {
              anyChange = tiVar.Update(Join(tiVar.CurrentValue, bValue)) || anyChange;
            }
          }
        }
      } while (anyChange);
    }
  }
}
