//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public interface TypeImprovement {

  }

  public class TypeImprover : ResolverPass {
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
      if (member is ConstantField field) {
        if (field.Rhs != null) {
          VisitExpression(field.Rhs);
          Improve(field.TypeImprovement, field.Rhs.TypeImprovement);
        }

      } else if (member is Method method) {
        foreach (var formal in method.Ins) {
          if (formal.DefaultValue != null) {
            VisitExpression(formal.DefaultValue);
          }
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

    void Improve(TypeImprovement target, TypeImprovement rhs) {
      // TODO: this should, more or less, set target to Meet(target, rhs)
    }

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
      // TODO
    }

    void VisitStatement(Statement stmt) {

    }
  }
}
