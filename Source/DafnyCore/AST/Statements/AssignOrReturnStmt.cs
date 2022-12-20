using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AssignOrReturnStmt : ConcreteUpdateStatement {
  public readonly Expression Rhs; // this is the unresolved RHS, and thus can also be a method call
  public readonly List<AssignmentRhs> Rhss;
  public readonly AttributedToken KeywordToken;
  [FilledInDuringResolution] public readonly List<Statement> ResolvedStatements = new List<Statement>();
  public override IEnumerable<Statement> SubStatements {
    get { return ResolvedStatements; }
  }

  public override IEnumerable<INode> Children => ResolvedStatements;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Lhss != null);
    Contract.Invariant(
      Lhss.Count == 0 ||                   // ":- MethodOrExpresion;" which returns void success or an error
      (Lhss.Count == 1 && Lhss[0] != null)   // "y :- MethodOrExpression;"
    );
    Contract.Invariant(Rhs != null);
  }

  public AssignOrReturnStmt(IToken tok, IToken endTok, List<Expression> lhss, Expression rhs, AttributedToken keywordToken, List<AssignmentRhs> rhss = null)
    : base(tok, endTok, lhss) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(lhss != null);
    Contract.Requires(lhss.Count <= 1);
    Contract.Requires(rhs != null);
    Rhs = rhs;
    Rhss = rhss;
    KeywordToken = keywordToken;
  }
}