package ink.sora

def lower(syntaxNode: SyntaxNode): SyntaxNode =
  syntaxNode match
    case BinOp(t) =>
      t.lhs = lower(t.lhs)
      t.rhs = lower(t.rhs)
      t
    case UnOp(t) =>
      t.subject = lower(t.subject)
      t
    case SyntaxNode.TypeAlias(_, _) | SyntaxNode.Bool(_) | SyntaxNode.Number(_) | SyntaxNode.Id(_) | SyntaxNode.Unit => syntaxNode
    case SyntaxNode.Abstraction(binder, binderType, body) =>
      SyntaxNode.Abstraction(binder, binderType, lower(body))
    case SyntaxNode.Application(f, a) =>
      SyntaxNode.Application(lower(f), lower(a))
    case SyntaxNode.Tuple(items) =>
      SyntaxNode.Tuple(items.map(lower))
    case SyntaxNode.If(cond, thenBranch, elseBranch) =>
      SyntaxNode.If(lower(cond), lower(thenBranch), lower(elseBranch))
    case SyntaxNode.LetBinding(isRec, binder, binderType, binderExpr, body) =>
      val loweredBinderExpr = lower(binderExpr)
      val loweredBody = body.map(lower)
      if isRec then
        binderType.getOrElse(throw error("Recursive definition requires type annotation"))
        SyntaxNode.LetBinding(false, binder, binderType,
          SyntaxNode.Fixpoint(SyntaxNode.Abstraction(binder, binderType, loweredBinderExpr)), loweredBody)
      else
        SyntaxNode.LetBinding(false, binder, binderType, loweredBinderExpr, loweredBody)
    case SyntaxNode.Fixpoint(f) =>
      SyntaxNode.Fixpoint(lower(f))
    case _ => throw IllegalStateException("Unexpected syntax node " + syntaxNode)