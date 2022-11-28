package ink.sora

private def reduceBinary[T <: SyntaxNode & BinaryOperator](context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using reducer: BinaryReducer[T]): SyntaxNode =
  reducer.reduce(context, lhs, rhs)

private def reduceUnary[T <: SyntaxNode & UnaryOperator](context: SymbolContext, subject: SyntaxNode)(using reducer: UnaryReducer[T]): SyntaxNode =
  reducer.reduce(context, subject)

class WeakNormalHeadNormalizer:
  def reduce(context: SymbolContext, syntaxNode: SyntaxNode)(using eq: Equalizer): SyntaxNode =
    return syntaxNode match
      case SyntaxNode.Addition(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of addition operator must be nat")
        else reduceBinary[SyntaxNode.Addition](context, lhs, rhs)
      case SyntaxNode.Subtraction(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of subtraction operator must be nat")
        else reduceBinary[SyntaxNode.Subtraction](context, lhs, rhs)
      case SyntaxNode.Multiplication(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of multiplication operator must be nat")
        else reduceBinary[SyntaxNode.Multiplication](context, lhs, rhs)
      case SyntaxNode.Division(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of division operator must be nat")
        else reduceBinary[SyntaxNode.Division](context, lhs, rhs)
      case SyntaxNode.Equal(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) != typeOfUnwrapped(context, rhs) then
          throw error("The operands of equality operator must have the same type")
        else reduceBinary[SyntaxNode.Equal](context, lhs, rhs)
      case SyntaxNode.NotEqual(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) != typeOfUnwrapped(context, rhs) then
          throw error("The operands of inequality operator must have the same type")
        else reduceBinary[SyntaxNode.NotEqual](context, lhs, rhs)
      case SyntaxNode.Negation(subject) =>
        if typeOfUnwrapped(context, subject) != TypeDecl.BoolType then
          throw error("The operand of negation operator must be bool")
        else reduceUnary[SyntaxNode.Negation](context, subject)
      case SyntaxNode.Conjunction(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.BoolType -> TypeDecl.BoolType then
          throw error("The operands of conjunction operator must be bool")
        else reduceBinary[SyntaxNode.Conjunction](context, lhs, rhs)
      case SyntaxNode.Disjunction(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.BoolType -> TypeDecl.BoolType then
          throw error("The operands of disjunction operator must be bool")
        else reduceBinary[SyntaxNode.Disjunction](context, lhs, rhs)
      case SyntaxNode.LessThan(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of less-than operator must be nat")
        else reduceBinary[SyntaxNode.LessThan](context, lhs, rhs)
      case SyntaxNode.GreaterThan(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of greater-than operator must be nat")
        else reduceBinary[SyntaxNode.GreaterThan](context, lhs, rhs)
      case SyntaxNode.LessThanEqual(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of less-than-or-equal operator must be nat")
        else reduceBinary[SyntaxNode.LessThanEqual](context, lhs, rhs)
      case SyntaxNode.GreaterThanEqual(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.NatType -> TypeDecl.NatType then
          throw error("The operands of greater-than-or-equal operator must be nat")
        else reduceBinary[SyntaxNode.GreaterThanEqual](context, lhs, rhs)
      case SyntaxNode.Projection(lhs, rhs) =>
        if typeOfUnwrapped(context, lhs) -> typeOfUnwrapped(context, rhs) != TypeDecl.ProductType -> TypeDecl.NatType then
          throw error("The left operand of projection operator must be a product type")
        else reduceBinary[SyntaxNode.Projection](context, lhs, rhs)
      case SyntaxNode.Sequence(lhs, rhs) => reduceBinary[SyntaxNode.Sequence](context, lhs, rhs)
      case SyntaxNode.Fixpoint(subject) => reduceUnary[SyntaxNode.Fixpoint](context, subject)
      case SyntaxNode.TypeAlias(_, _) => throw error("Type aliases cannot appear in this context")
      case SyntaxNode.Tuple(products) => SyntaxNode.Tuple(products.map(reduce(context, _)))
      case SyntaxNode.Id(name) => context.lookupAssignBinding(name).getOrElse(throw error(s"Unresolved symbol $name"))
      case SyntaxNode.Number(_) | SyntaxNode.Bool(_) | SyntaxNode.Unit => syntaxNode
      case SyntaxNode.If(cond, thenClause, elseClause) =>
        val condReduced = reduce(context, cond)
        val thenClauseReduced = reduce(context, thenClause)
        val elseClauseReduced = reduce(context, elseClause)
        condReduced match
          case SyntaxNode.Bool(value) => if value then thenClauseReduced else elseClauseReduced
          case _ => SyntaxNode.If(condReduced, thenClauseReduced, elseClauseReduced)
      case SyntaxNode.Application(SyntaxNode.Abstraction(binder, binderType, body), argument) =>
        val argType = typeOfUnwrapped(context, argument)
        if binderType.isDefined && !eq.typeEquiv(context, argType, binderType.get) then
          throw error(s"Types mismatch: expecting ${pprint(binderType.get)}, got ${pprint(argType)}")
        substituteTerm(body, binder, argument)
      case SyntaxNode.Application(lhs, rhs) => SyntaxNode.Application(reduce(context, lhs), rhs)
      case SyntaxNode.Abstraction(_, _, _) => syntaxNode
      case SyntaxNode.LetBinding(_, binder, binderType, binderExpr, body) =>
        val binderExprType = typeOfUnwrapped(context, binderExpr)
        if body.isDefined then
          if binderType.isDefined && !eq.typeEquiv(context, binderType.get, binderExprType) then
            throw error(s"Types mismatch: expecting ${pprint(binderType.get)}, got ${pprint(binderExprType)}")
          substituteTerm(body.get, binder, binderExpr)
        else
          throw error("Scope-less let bindings are only supposed to occur at top-level")

given WeakNormalHeadNormalizer = new WeakNormalHeadNormalizer()

trait BinaryReducer[T <: SyntaxNode & BinaryOperator]:
  def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode

trait UnaryReducer[T <: SyntaxNode & UnaryOperator]:
  def reduce(context: SymbolContext, subject: SyntaxNode)(using WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode

given BinaryReducer[SyntaxNode.Addition] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Number(lhsN + rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.Addition(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Subtraction] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Number(if lhsN - rhsN >= 0 then lhsN - rhsN else 0)
        case (lhsReduced, rhsReduced) => SyntaxNode.Subtraction(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Multiplication] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Number(lhsN * rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.Multiplication(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Division] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Number(if rhsN != 0 then lhsN / rhsN else throw error("Divisor cannot be zero"))
        case (lhsReduced, rhsReduced) => SyntaxNode.Division(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Equal] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using WeakNormalHeadNormalizer)(using eq: Equalizer): SyntaxNode =
    SyntaxNode.Bool(eq.termEquiv(context, lhs, rhs))

given BinaryReducer[SyntaxNode.NotEqual] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using WeakNormalHeadNormalizer)(using eq: Equalizer): SyntaxNode =
    SyntaxNode.Bool(!eq.termEquiv(context, lhs, rhs))

given BinaryReducer[SyntaxNode.Conjunction] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
        case (SyntaxNode.Bool(lhsB), SyntaxNode.Bool(rhsB)) => SyntaxNode.Bool(lhsB && rhsB)
        case (lhsReduced, rhsReduced) => SyntaxNode.Conjunction(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Disjunction] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
        case (SyntaxNode.Bool(lhsB), SyntaxNode.Bool(rhsB)) => SyntaxNode.Bool(lhsB || rhsB)
        case (lhsReduced, rhsReduced) => SyntaxNode.Disjunction(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.LessThan] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Bool(lhsN < rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.LessThan(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.LessThanEqual] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Bool(lhsN <= rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.LessThanEqual(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.GreaterThan] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Bool(lhsN > rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.GreaterThan(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.GreaterThanEqual] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
        case (SyntaxNode.Number(lhsN), SyntaxNode.Number(rhsN)) => SyntaxNode.Bool(lhsN >= rhsN)
        case (lhsReduced, rhsReduced) => SyntaxNode.GreaterThanEqual(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Projection] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return (whr.reduce(context, lhs), whr.reduce(context, rhs)) match
      case (SyntaxNode.Tuple(products), SyntaxNode.Number(value)) =>
        if products.indices contains value then
          products(value)
        else throw error("Tuple index out of bounds")
      case (lhsReduced, rhsReduced) => SyntaxNode.Projection(lhsReduced, rhsReduced)

given BinaryReducer[SyntaxNode.Sequence] with
  override def reduce(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    whr.reduce(context, lhs)
    return whr.reduce(context, rhs)

given UnaryReducer[SyntaxNode.Negation] with
  override def reduce(context: SymbolContext, subject: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode =
    return whr.reduce(context, subject) match
        case SyntaxNode.Bool(value) => SyntaxNode.Bool(!value)
        case reduced => SyntaxNode.Negation(reduced)

given UnaryReducer[SyntaxNode.Fixpoint] with
  override def reduce(context: SymbolContext, subject: SyntaxNode)(using whr: WeakNormalHeadNormalizer)(using Equalizer): SyntaxNode = subject

@main
def main(): Unit =
  for tokens <- Lexer(
    """
      |let a = true in
      |  let b = 3 in
      |    let c = 2 in
      |      (fun x: Vector [x + 1]. x) vec
      |    end
      |  end
      |end""".stripMargin) do
    val syntax = Parser(tokens).program()
    val context = SymbolContext()
      .addAliasBinding("Vector", TypeDecl.DependentOperator("n", TypeDecl.NatType, TypeDecl.PiType("x", TypeDecl.NatType, TypeDecl.NatType)))
      .addTermBinding("vec", TypeDecl.DependentInstantiation(TypeDecl.Var("Vector"), SyntaxNode.Number(2)))
    println(pprint(typeOf(context, SyntaxNode.Id("vec")).get))
    val normalizer = new WeakNormalHeadNormalizer()
    var reduced = normalizer.reduce(context, syntax.head)
    println(pprint(syntax.head))
    println("---------------------------")
    for _ <- 1 to 10 do
      reduced = normalizer.reduce(context, reduced)
      println(pprint(reduced))
      println("---------------------------")