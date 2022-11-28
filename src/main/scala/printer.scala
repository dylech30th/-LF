package ink.sora

import SyntaxNode.*
import TypeDecl.*

import scala.annotation.tailrec
import scala.collection.mutable
import scala.reflect.ClassTag

trait Show[T]:
  def show(t: T): String

given Show[SyntaxNode] with
  private enum Associativity:
    case Left
    case Right
    case None

  private val assocTable: Map[List[Class[_ <: SyntaxNode]], Associativity] =
    Map(
      (classOf[Negation] :: Nil) -> Associativity.None,
      (classOf[Projection] ::
        classOf[Multiplication] ::
        classOf[Division] ::
        classOf[Addition] ::
        classOf[Subtraction] ::
        classOf[LessThan] ::
        classOf[LessThanEqual] ::
        classOf[GreaterThan] ::
        classOf[GreaterThanEqual] ::
        classOf[Conjunction] ::
        classOf[Disjunction] ::
        classOf[Equal] ::
        classOf[Application] ::
        classOf[NotEqual] :: Nil) -> Associativity.Left,
      (classOf[Fixpoint] :: Nil) -> Associativity.None,
      (classOf[Sequence] :: Nil) -> Associativity.Right
    )

  private val precedenceTable: Map[List[Class[_ <: SyntaxNode]], Int] =
    Map(
      (classOf[Negation] :: Nil) -> 0,
      (classOf[Projection] :: Nil) -> 1,
      (classOf[Multiplication] :: classOf[Division] :: Nil) -> 2,
      (classOf[Addition] :: classOf[Subtraction] :: Nil) -> 3,
      (classOf[LessThan] :: classOf[LessThanEqual] :: classOf[GreaterThan] :: classOf[GreaterThanEqual] :: Nil) -> 4,
      (classOf[Conjunction] :: classOf[Disjunction] :: Nil) -> 5,
      (classOf[Equal] :: classOf[NotEqual] :: Nil) -> 6,
      (classOf[Sequence] :: Nil) -> 7,
      (classOf[Abstraction] :: Nil) -> 8,
      (classOf[Application] :: classOf[Fixpoint] :: Nil) -> 9
    )

  private def precedenceOf[T <: SyntaxNode: ClassTag]: Int =
    precedenceOf(implicitly[ClassTag[T]].runtimeClass)

  private def precedenceOf[T](clazz: Class[T]): Int =
    precedenceTable.find(_._1.contains(clazz)).map(_._2).getOrElse(0)

  private def associativityOf[T <: SyntaxNode: ClassTag]: Associativity =
    associativityOf(implicitly[ClassTag[T]].runtimeClass)

  private def associativityOf[T](clazz: Class[T]): Associativity =
    assocTable.find(_._1.contains(clazz)).map(_._2).getOrElse(Associativity.None)

  private def showAssoc[T <: BinaryOperator & SyntaxNode : ClassTag](binOp: T, sign: String): String =
    val delimiter = if sign.isBlank then " " else s" $sign "
    return (binOp, associativityOf[T]) match
      case (BinOpLeftNotSingleton(_), Associativity.Right) =>
        s"${show(binOp.lhs, precedenceOf[T], true)}$delimiter${show(binOp.rhs, precedenceOf[T])}"
      case (BinOpRightNotSingleton(_), Associativity.Left) =>
        s"${show(binOp.lhs, precedenceOf[T])}$delimiter${show(binOp.rhs, precedenceOf[T], true)}"
      case _ =>
        s"${show(binOp.lhs, precedenceOf[T])}$delimiter${show(binOp.rhs, precedenceOf[T])}"

  private def show(t: SyntaxNode, parentPrecedence: Int, shouldQuoteSelf: Boolean = false, indentLevel: Int = 0): String =
    def indent(level: Int): String = "  " * level
    val internal = t match
      case LetBinding(_, letBinder, _, Fixpoint(Abstraction(_, binderType, body)), Some(letBody)) =>
        s"""let rec $letBinder: ${pprint(binderType.get)} = ${show(body)} in
           |${indent(indentLevel + 1)}${show(letBody, parentPrecedence, shouldQuoteSelf, indentLevel + 1)}
           |${indent(indentLevel)}end\n""".stripMargin
      case LetBinding(_, binder, binderType, binderExpr, Some(body)) =>
        s"""let $binder${binderType.map(ty => s": ${pprint(ty)}").getOrElse("")} = ${show(binderExpr)} in
           |${indent(indentLevel + 1)}${show(body, parentPrecedence, shouldQuoteSelf, indentLevel + 1)}
           |${indent(indentLevel)}end""".stripMargin
      case LetBinding(_, binder, binderType, binderExpr, None) =>
        s"let $binder${binderType.map(ty => s": ${pprint(ty)}").getOrElse("")} = ${show(binderExpr)}"
      case Negation(subject) =>
        s"!${show(subject, precedenceOf[Negation])}"
      case add@Addition(_, _) => showAssoc[Addition](add, "+")
      case sub@Subtraction(_, _) => showAssoc[Subtraction](sub, "-")
      case mul@Multiplication(_, _) => showAssoc[Multiplication](mul, "*")
      case div@Division(_, _) => showAssoc[Division](div, "/")
      case eq@Equal(_, _) => showAssoc[Equal](eq, "==")
      case ne@NotEqual(_, _) => showAssoc[NotEqual](ne, "!=")
      case and@Conjunction(_, _) => showAssoc[Conjunction](and, "&&")
      case or@Disjunction(_, _) => showAssoc[Disjunction](or, "||")
      case lt@LessThan(_, _) => showAssoc[LessThan](lt, "<")
      case gt@GreaterThan(_, _) => showAssoc[GreaterThan](gt, ">")
      case lte@LessThanEqual(_, _) => showAssoc[LessThanEqual](lte, "<=")
      case gte@GreaterThanEqual(_, _) => showAssoc[GreaterThanEqual](gte, ">=")
      case pj@Projection(_, _) => showAssoc[Projection](pj, ".")
      case seq@Sequence(_, _) => showAssoc[Sequence](seq, ";")
      case app@Application(_, _) => showAssoc[Application](app, " ")
      case Number(value) => s"$value"
      case Bool(value) => s"$value"
      case SyntaxNode.Unit => "unit"
      case Id(value) => value
      case If(cond, thenClause, elseClause) =>
        s"""if ${show(cond)} then
          |${indent(indentLevel + 1)}${show(thenClause, parentPrecedence, shouldQuoteSelf, indentLevel + 1)}
          |${indent(indentLevel)}else
          |${indent(indentLevel + 1)}${show(elseClause, parentPrecedence, shouldQuoteSelf, indentLevel + 1)}""".stripMargin
      case Tuple(products) => s"(${products.map(show).mkString(", ")})"
      case Abstraction(binder, binderType, body) => s"(λ$binder${binderType.map(ty => s": ${pprint(ty)}").getOrElse("")}. ${show(body)})"
      case TypeAlias(name, alias) => s"type $name = ${pprint(alias)}"
      case Fixpoint(_) => throw error("Fixpoint is language-intrinsic and should not be printed")
      case TypeDefine(binder, kind) => s"define $binder :: ${pprint(kind)}"
      case TermDefine(binder, ty) => s"define $binder: ${pprint(ty)}"
      case Macro(name, target) => s"#$name(${show(target)})"

    val hasLowerPrecedence = 0 until precedenceOf(t.getClass) contains parentPrecedence
    val atLeastPrecedence = 0 to precedenceOf(t.getClass) contains parentPrecedence
    return if ((shouldQuoteSelf && atLeastPrecedence) || hasLowerPrecedence) && !t.isInstanceOf[UnaryOperator] then
      s"($internal)"
    else internal

  def show(t: SyntaxNode): String = show(t, -1)
end given

given Show[TypeDecl] with
  override def show(t: TypeDecl): String = t match
    case UnitType => "unit"
    case BoolType => "bool"
    case NatType => "nat"
    case Var(name) => name
    case PiType(binder, binderType, body) =>
      if fvDep(body) contains binder then
        s"Π$binder: ${show(binderType)}. ${pprint(body)}"
      else
        body match
          case NotSingletonType(_) => s"${show(binderType)} -> (${pprint(body)})"
          case _ => s"${show(binderType)} -> ${pprint(body)}"
    case SigmaType(binder, binderType, body) =>
      if fvDep(body) contains binder then
        s"Σ$binder: ${show(binderType)}. ${pprint(body)}"
      else
        body match
          case NotSingletonType(_) => s"${show(binderType)} * (${pprint(body)})"
          case _ => s"${show(binderType)} * ${pprint(body)}"
    case DependentOperator(binder, binderType, body) =>
      body match
        case NotSingletonType(_) => s"λ$binder: ${show(binderType)}. (${pprint(body)})"
        case _ => s"λ$binder: ${show(binderType)}. ${pprint(body)}"
    case ProductType(products) => s"(${products.map(show).mkString(" * ")})"
    case DependentInstantiation(f, a) =>
      s"${show(f)} [${pprint(a)}]"

given Show[Kind] with
  override def show(t: Kind): String = t match
    case Kind.Type => "*"
    case Kind.Pi(_, binderType, bodyKind) => s"${pprint(binderType)} -> ${show(bodyKind)}"

def pprint[T](t: T)(using s: Show[T]): String = s.show(t)