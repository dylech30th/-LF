package ink.sora

import scala.annotation.tailrec

private def reduceBinary[T <: SyntaxNode & BinaryOperator](context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using reducer: BinaryReducer[T]): SyntaxNode =
  reducer.reduce(context, macros, lhs, rhs)

private def reduceUnary[T <: SyntaxNode & UnaryOperator](context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], subject: SyntaxNode)(using reducer: UnaryReducer[T]): SyntaxNode =
  reducer.reduce(context, macros, subject)

object WeakNormalHeadNormalizer:
  def reduce(context: SymbolContext, syntaxNode: SyntaxNode, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], topLevel: Boolean = false)(using eq: Equalizer): SyntaxNode =
    return syntaxNode match
      case SyntaxNode.Macro(name, target) =>
        macros.get(name).fold(())(_(target, context))
        syntaxNode
      case SyntaxNode.Addition(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of addition operator must be nat")
        else reduceBinary[SyntaxNode.Addition](context, macros, lhs, rhs)
      case SyntaxNode.Subtraction(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of subtraction operator must be nat")
        else reduceBinary[SyntaxNode.Subtraction](context, macros, lhs, rhs)
      case SyntaxNode.Multiplication(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of multiplication operator must be nat")
        else reduceBinary[SyntaxNode.Multiplication](context, macros, lhs, rhs)
      case SyntaxNode.Division(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of division operator must be nat")
        else reduceBinary[SyntaxNode.Division](context, macros, lhs, rhs)
      case SyntaxNode.Equal(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) != typeOfUnwrapped(context, rhs, macros) then
          throw error("The operands of equality operator must have the same type")
        else reduceBinary[SyntaxNode.Equal](context, macros, lhs, rhs)
      case SyntaxNode.NotEqual(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) != typeOfUnwrapped(context, rhs, macros) then
          throw error("The operands of inequality operator must have the same type")
        else reduceBinary[SyntaxNode.NotEqual](context, macros, lhs, rhs)
      case SyntaxNode.Negation(subject) =>
        if typeOfUnwrapped(context, subject, macros) != TypeDecl.BoolType then
          throw error("The operand of negation operator must be bool")
        else reduceUnary[SyntaxNode.Negation](context, macros, subject)
      case SyntaxNode.Conjunction(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.BoolType -> TypeDecl.BoolType then
          throw error("The operands of conjunction operator must be bool")
        else reduceBinary[SyntaxNode.Conjunction](context, macros, lhs, rhs)
      case SyntaxNode.Disjunction(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.BoolType -> TypeDecl.BoolType then
          throw error("The operands of disjunction operator must be bool")
        else reduceBinary[SyntaxNode.Disjunction](context, macros, lhs, rhs)
      case SyntaxNode.LessThan(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of less-than operator must be nat")
        else reduceBinary[SyntaxNode.LessThan](context, macros, lhs, rhs)
      case SyntaxNode.GreaterThan(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of greater-than operator must be nat")
        else reduceBinary[SyntaxNode.GreaterThan](context, macros, lhs, rhs)
      case SyntaxNode.LessThanEqual(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of less-than-or-equal operator must be nat")
        else reduceBinary[SyntaxNode.LessThanEqual](context, macros, lhs, rhs)
      case SyntaxNode.GreaterThanEqual(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of greater-than-or-equal operator must be nat")
        else reduceBinary[SyntaxNode.GreaterThanEqual](context, macros, lhs, rhs)
      case SyntaxNode.Projection(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs, macros) -> typeOfUnwrapped(context, rhs, macros) != TypeDecl.ProductType -> TypeDecl.NatType then
          throw error("The left operand of projection operator must be a product type")
        else reduceBinary[SyntaxNode.Projection](context, macros, lhs, rhs)
      case SyntaxNode.Sequence(lhs, rhs) => reduceBinary[SyntaxNode.Sequence](context, macros, lhs, rhs)
      case SyntaxNode.Fixpoint(subject) => reduceUnary[SyntaxNode.Fixpoint](context, macros, subject)
      case SyntaxNode.TypeAlias(_, _) => throw error("Type aliases cannot appear in this context")
      case SyntaxNode.Tuple(products) => SyntaxNode.Tuple(products.map(reduce(context, _, macros)))
      case SyntaxNode.Id(name) => context.lookupAssignBinding(name).getOrElse(syntaxNode)
      case SyntaxNode.Number(_) | SyntaxNode.Bool(_) | SyntaxNode.Unit => syntaxNode
      case SyntaxNode.If(cond, thenClause, elseClause) =>
        val condReduced = reduce(context, cond, macros)
        val thenClauseReduced = reduce(context, thenClause, macros)
        val elseClauseReduced = reduce(context, elseClause, macros)
        condReduced match
          case SyntaxNode.Bool(value) => if value then thenClauseReduced else elseClauseReduced
          case _ => SyntaxNode.If(condReduced, thenClauseReduced, elseClauseReduced)
      case SyntaxNode.Application(SyntaxNode.Abstraction(binder, binderType, body), argument) =>
        val argType = typeOfUnwrapped(context, argument, macros)
        if binderType.isDefined && !eq.typeEquiv(context, macros, argType, binderType.get) then
          throw error(s"Types mismatch: expecting ${pprint(binderType.get)}, got ${pprint(argType)}")
        substituteTerm(body, binder, argument)
      case SyntaxNode.Application(lhs, rhs) =>
        SyntaxNode.Application(reduce(context, lhs, macros), rhs)
      case SyntaxNode.Abstraction(_, _, _) | SyntaxNode.TypeDefine(_, _) | SyntaxNode.TermDefine(_, _) => syntaxNode
      case SyntaxNode.LetBinding(_, binder, binderType, binderExpr, body) =>
        val bt = binderType.getOrElse(typeOf(context, binderExpr, macros).get)
        val binderExprType = typeOfUnwrapped(context, binderExpr, macros)
        if body.isDefined then
          if binderType.isDefined && !eq.typeEquiv(context, macros, bt, binderExprType) then
            throw error(s"Types mismatch: expecting ${pprint(bt)}, got ${pprint(binderExprType)}")
          substituteTerm(body.get, binder, binderExpr)
        else if topLevel then
          SyntaxNode.LetBinding(false, binder, Some(bt), reduce(context, binderExpr, macros), body)
        else throw error("Scope-less let bindings are only supposed to occur at top-level")

  @tailrec
  def normalize(context: SymbolContext, syntaxNode: SyntaxNode, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], topLevel: Boolean = false)(using Equalizer): SyntaxNode =
    val reduced = reduce(context, syntaxNode, macros, topLevel)
    if reduced == syntaxNode then reduced else normalize(context, reduced, macros)

  def normalize(context: SymbolContext, syntaxNode: List[SyntaxNode], macros: Map[String, (SyntaxNode, SymbolContext) => Unit])(using Equalizer): List[SyntaxNode] =
    for node <- syntaxNode yield
      normalize(context, node, macros, true).run {
        case SyntaxNode.TypeDefine(binder, kind) => context.addTypeBinding(TypeDecl.Var(binder), kind)
        case SyntaxNode.TermDefine(binder, ty) => context.addTermBinding(binder, ty)
        case SyntaxNode.LetBinding(_, binder, binderType, binderExpr, None) =>
          context.addTermBinding(binder, binderType.getOrElse(typeOf(context, binderExpr, macros).get))
          context.addAssignBinding(binder, binderExpr)
        case _ => ()
      }

trait BinaryReducer[T <: SyntaxNode & BinaryOperator]:
  protected val whr: WeakNormalHeadNormalizer.type = WeakNormalHeadNormalizer

  def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode

trait UnaryReducer[T <: SyntaxNode & UnaryOperator]:
  protected val whr: WeakNormalHeadNormalizer.type = WeakNormalHeadNormalizer

  def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], subject: SyntaxNode)(using Equalizer): SyntaxNode

given BinaryReducer[SyntaxNode.Addition] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Number(lhsN + rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.Addition(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Subtraction] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Number(if lhsN - rhsN >= 0 then lhsN - rhsN else 0)
        case (lhsReduced, rhsReduced) => SyntaxNode.Subtraction(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Multiplication] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Number(lhsN * rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.Multiplication(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Division] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Number(if rhsN != 0 then lhsN / rhsN else throw error("Divisor cannot be zero"))
        case (lhsReduced, rhsReduced) => SyntaxNode.Division(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Equal] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using eq: Equalizer): SyntaxNode =
    SyntaxNode.Bool(eq.termEquiv(context, macros, lhs, rhs))

given BinaryReducer[SyntaxNode.NotEqual] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using eq: Equalizer): SyntaxNode =
    SyntaxNode.Bool(!eq.termEquiv(context, macros, lhs, rhs))

given BinaryReducer[SyntaxNode.Conjunction] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
        case (SyntaxNode.Bool(lhsB), SyntaxNode.Bool(rhsB)) => SyntaxNode.Bool(lhsB && rhsB)
        case (lhsReduced, rhsReduced) => SyntaxNode.Conjunction(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Disjunction] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
        case (SyntaxNode.Bool(lhsB), SyntaxNode.Bool(rhsB)) => SyntaxNode.Bool(lhsB || rhsB)
        case (lhsReduced, rhsReduced) => SyntaxNode.Disjunction(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.LessThan] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Bool(lhsN < rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.LessThan(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.LessThanEqual] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Bool(lhsN <= rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.LessThanEqual(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.GreaterThan] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Bool(lhsN > rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.GreaterThan(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.GreaterThanEqual] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Bool(lhsN >= rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.GreaterThanEqual(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Projection] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs, macros), whr.reduce(context, rhs, macros)) match
      case (SyntaxNode.Tuple(products), SyntaxNode.Number(value)) =>
        if products.indices contains value then
          products(value)
        else throw error("Tuple index out of bounds")
      case (lhsReduced, rhsReduced) => SyntaxNode.Projection(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Sequence] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode)(using Equalizer): SyntaxNode =
    whr.reduce(context, lhs, macros)
    return whr.reduce(context, rhs, macros)

given UnaryReducer[SyntaxNode.Negation] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], subject: SyntaxNode)(using Equalizer): SyntaxNode =
    return whr.reduce(context, subject, macros) match
        case SyntaxNode.Bool(value) => SyntaxNode.Bool(!value)
        case reduced => SyntaxNode.Negation(reduced)

given UnaryReducer[SyntaxNode.Fixpoint] with
  override def reduce(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], subject: SyntaxNode)(using Equalizer): SyntaxNode = subject