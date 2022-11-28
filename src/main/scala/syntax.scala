package ink.sora

import Lexer.{parse, phrase, rep1}

import java.util.function.BinaryOperator
import scala.collection.mutable.ListBuffer
import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers


enum TokenKind:
  case Id
  case LessThan
  case GreaterThan
  case EqualEqual
  case LessThanEqual
  case GreaterThanEqual
  case AmpAmp
  case PipePipe
  case Pipe
  case NotEqual
  case Not
  case Number
  case Plus
  case Minus
  case Divides
  case Colon
  case Comma
  case RightParen
  case LeftParen
  case RightArrow
  case False
  case True
  case Else
  case Then
  case If
  case Dot
  case Lambda
  case Equal
  case Let
  case Semicolon
  case Pi
  case Sigma
  case End
  case In
  case Product
  case Unit
  case Bool
  case Nat
  case Index
  case Type
  case Rec
  case LeftBracket
  case RightBracket
  case Define
  case ColonColon
  case DoubleArrow
  case Sharp
end TokenKind

enum Token(val kind: TokenKind, val isExprStart: Boolean = false):
  case Id(name: String) extends Token(TokenKind.Id, true)
  case Number(value: Int) extends Token(TokenKind.Number, true)
  case LessThan extends Token(TokenKind.LessThan)
  case GreaterThan extends Token(TokenKind.GreaterThan)
  case EqualEqual extends Token(TokenKind.EqualEqual)
  case LessThanEqual extends Token(TokenKind.LessThanEqual)
  case GreaterThanEqual extends Token(TokenKind.GreaterThanEqual)
  case AmpAmp extends Token(TokenKind.AmpAmp)
  case PipePipe extends Token(TokenKind.PipePipe)
  case NotEqual extends Token(TokenKind.NotEqual)
  case Not extends Token(TokenKind.Not)
  case Pipe extends Token(TokenKind.Pipe)
  case Colon extends Token(TokenKind.Colon)
  case Comma extends Token(TokenKind.Comma)
  case RightParen extends Token(TokenKind.RightParen)
  case LeftParen extends Token(TokenKind.LeftParen, true)
  case RightArrow extends Token(TokenKind.RightArrow)
  case False extends Token(TokenKind.False, true)
  case True extends Token(TokenKind.True, true)
  case Else extends Token(TokenKind.Else)
  case Then extends Token(TokenKind.Then)
  case If extends Token(TokenKind.If, true)
  case Plus extends Token(TokenKind.Plus)
  case Minus extends Token(TokenKind.Minus)
  case Product extends Token(TokenKind.Product)
  case Divides extends Token(TokenKind.Divides)
  case Dot extends Token(TokenKind.Dot)
  case Lambda extends Token(TokenKind.Lambda, true)
  case Equal extends Token(TokenKind.Equal)
  case Let extends Token(TokenKind.Let, true)
  case Semicolon extends Token(TokenKind.Semicolon)
  case Pi extends Token(TokenKind.Pi)
  case Sigma extends Token(TokenKind.Sigma)
  case End extends Token(TokenKind.End)
  case In extends Token(TokenKind.In)
  case Unit extends Token(TokenKind.Unit)
  case Bool extends Token(TokenKind.Bool)
  case Nat extends Token(TokenKind.Nat)
  case Index(value: Either[String, Int]) extends Token(TokenKind.Index)
  case Type extends Token(TokenKind.Type)
  case Rec extends Token(TokenKind.Rec)
  case LeftBracket extends Token(TokenKind.LeftBracket)
  case RightBracket extends Token(TokenKind.RightBracket)
  case Define extends Token(TokenKind.Define)
  case ColonColon extends Token(TokenKind.ColonColon)
  case DoubleArrow extends Token(TokenKind.DoubleArrow)
  case Sharp extends Token(TokenKind.Sharp)
end Token

object Lexer extends RegexParsers:
  override protected val whiteSpace: Regex = "[ \n\t\r\f]+".r
  override def skipWhitespace: Boolean = true

  private def index: Parser[Token] = "_[a-zA-Z0-9]+".r ^^ (s => Token.Index(s.stripMargin('_').toIntOption.toRight(s.stripMargin('_'))))
  private def identifier: Parser[Token] = "[a-zA-Z][a-zA-Z0-9_]*|\\+|-|\\*|/".r ^^ (Token.Id(_))
  private def colon: Parser[Token] = ":" ^^ (_ => Token.Colon)
  private def comma: Parser[Token] = "," ^^ (_ => Token.Comma)
  private def leftParen: Parser[Token] = "(" ^^ (_ => Token.LeftParen)
  private def rightParen: Parser[Token] = ")" ^^ (_ => Token.RightParen)
  private def rightArrow: Parser[Token] = "->" ^^ (_ => Token.RightArrow)
  private def `false`: Parser[Token] = "false" ^^ (_ => Token.False)
  private def `true`: Parser[Token] = "true" ^^ (_ => Token.True)
  private def number: Parser[Token] = "[0-9]+".r ^^ (x => Token.Number(x.toInt))
  private def `type`: Parser[Token] = "type" ^^ (_ => Token.Type)
  private def `else`: Parser[Token] = "else" ^^ (_ => Token.Else)
  private def `then`: Parser[Token] = "then" ^^ (_ => Token.Then)
  private def `if`: Parser[Token] = "if" ^^ (_ => Token.If)
  private def dot: Parser[Token] = "." ^^ (_ => Token.Dot)
  private def lambda: Parser[Token] = "fun|λ".r ^^ (_ => Token.Lambda)
  private def equal: Parser[Token] = "=" ^^ (_ => Token.Equal)
  private def let: Parser[Token] = "let" ^^ (_ => Token.Let)
  private def semicolon: Parser[Token] = ";" ^^ (_ => Token.Semicolon)
  private def pi: Parser[Token] = "pi|Π".r ^^ (_ => Token.Pi)
  private def sigma: Parser[Token] = "sigma|Σ".r ^^ (_ => Token.Sigma)
  private def end: Parser[Token] = "end" ^^ (_ => Token.End)
  private def in: Parser[Token] = "in" ^^ (_ => Token.In)
  private def unit: Parser[Token] = "unit" ^^ (_ => Token.Unit)
  private def bool: Parser[Token] = "bool" ^^ (_ => Token.Bool)
  private def nat: Parser[Token] = "nat" ^^ (_ => Token.Nat)
  private def add: Parser[Token] = "+" ^^ (_ => Token.Plus)
  private def minus: Parser[Token] = "-" ^^ (_ => Token.Minus)
  private def product: Parser[Token] = "*" ^^ (_ => Token.Product)
  private def divides: Parser[Token] = "/" ^^ (_ => Token.Divides)
  private def lessThanEqual: Parser[Token] = "<=" ^^ (_ => Token.LessThanEqual)
  private def greaterThanEqual: Parser[Token] = ">=" ^^ (_ => Token.GreaterThanEqual)
  private def lessThan: Parser[Token] = "<" ^^ (_ => Token.LessThan)
  private def greaterThan: Parser[Token] = ">" ^^ (_ => Token.GreaterThan)
  private def equalEqual: Parser[Token] = "==" ^^ (_ => Token.EqualEqual)
  private def ampAmp: Parser[Token] = "&&" ^^ (_ => Token.AmpAmp)
  private def pipePipe: Parser[Token] = "||" ^^ (_ => Token.PipePipe)
  private def pipe: Parser[Token] = "|" ^^ (_ => Token.Pipe)
  private def notEqual: Parser[Token] = "!=" ^^ (_ => Token.NotEqual)
  private def not: Parser[Token] = "!" ^^ (_ => Token.Not)
  private def rec: Parser[Token] = "rec" ^^ (_ => Token.Rec)
  private def leftBracket: Parser[Token] = "[" ^^ (_ => Token.LeftBracket)
  private def rightBracket: Parser[Token] = "]" ^^ (_ => Token.RightBracket)
  private def define: Parser[Token] = "define" ^^ (_ => Token.Define)
  private def colonColon: Parser[Token] = "::" ^^ (_ => Token.ColonColon)
  private def doubleArrow: Parser[Token] = "=>" ^^ (_ => Token.DoubleArrow)
  private def sharp: Parser[Token] = "#" ^^ (_ => Token.Sharp)

  def tokens: Parser[List[Token]] =
    return phrase(rep1(
      lessThanEqual
        | sharp
        | doubleArrow
        | define
        | greaterThanEqual
        | rightArrow
        | lessThan
        | greaterThan
        | equalEqual
        | equal
        | notEqual
        | not
        | ampAmp
        | pipePipe
        | pipe
        | add
        | minus
        | divides
        | unit
        | bool
        | nat
        | colonColon
        | colon
        | comma
        | leftParen
        | rightParen
        | `false`
        | `true`
        | number
        | `type`
        | `else`
        | `then`
        | `if`
        | product
        | dot
        | lambda
        | let
        | semicolon
        | pi
        | sigma
        | end
        | in
        | index
        | rec
        | leftBracket
        | rightBracket
        | identifier))
  end tokens

  def apply(source: String): Either[String, List[Token]] =
    return parse(tokens, source) match
      case Success(result, _) => Right(result)
      case NoSuccess(msg, _) => Left(msg)
      case _ => throw IllegalStateException()
  end apply
end Lexer

trait BinaryOperator:
  var lhs: SyntaxNode
  var rhs: SyntaxNode

trait UnaryOperator:
  var subject: SyntaxNode

enum SyntaxNode:
  case Fixpoint(var subject: SyntaxNode) extends SyntaxNode with UnaryOperator
  case Addition(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case Subtraction(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case Multiplication(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case Division(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case Equal(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case NotEqual(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case Negation(var subject: SyntaxNode) extends SyntaxNode with UnaryOperator
  case Conjunction(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case Disjunction(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case LessThan(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case GreaterThan(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case LessThanEqual(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case GreaterThanEqual(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case Projection(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case Sequence(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case Application(var lhs: SyntaxNode, var rhs: SyntaxNode) extends SyntaxNode with BinaryOperator
  case TypeAlias(name: String, ty: TypeDecl)
  case Tuple(products: List[SyntaxNode])
  case Id(name: String)
  case Number(value: Int)
  case Bool(value: Boolean)
  case Unit
  case If(cond: SyntaxNode, thenClause: SyntaxNode, elseClause: SyntaxNode)
  case LetBinding(isRec: Boolean, binder: String, binderType: Option[TypeDecl], binderExpr: SyntaxNode, body: Option[SyntaxNode])
  case Abstraction(binder: String, binderType: Option[TypeDecl], body: SyntaxNode)
  case TypeDefine(binder: String, kind: Kind)
  case TermDefine(binder: String, ty: TypeDecl)
  case Macro(name: String, target: SyntaxNode)
end SyntaxNode

enum TypeDecl:
  case UnitType
  case BoolType
  case NatType
  case PiType(binder: String, binderType: TypeDecl, body: TypeDecl)
  case SigmaType(binder: String, binderType: TypeDecl, body: TypeDecl)
  case ProductType(products: List[TypeDecl])
  case DependentOperator(binder: String, binderType: TypeDecl, body: TypeDecl)
  case Var(name: String)
  case DependentInstantiation(f: TypeDecl, a: SyntaxNode)
end TypeDecl

class Parser(private var tokens: List[Token]):
  private def matchToken(tokenKind: TokenKind): Token =
    if tokens.head.kind == tokenKind then
      val head = tokens.head
      tokens = tokens.tail
      return head
    else
      System.err.println(tokens)
      throw IllegalStateException("Expecting token of kind " + tokenKind + " but got " + tokens.head.kind)

  def program(): List[SyntaxNode] =
    val es = ListBuffer.empty[SyntaxNode]
    while tokens.nonEmpty do
      es += (tokens.head.kind match
        case TokenKind.Type => typeAlias()
        case TokenKind.Define => define()
        case _ => lower(expr()))
    return es.toList

  private def define(): SyntaxNode =
    matchToken(TokenKind.Define)
    val binder = matchToken(TokenKind.Id).asInstanceOf[Token.Id].name
    return tokens.head match
      case Token.ColonColon =>
        matchToken(TokenKind.ColonColon)
        SyntaxNode.TypeDefine(binder, kind())
      case Token.Colon =>
        matchToken(TokenKind.Colon)
        SyntaxNode.TermDefine(binder, typeDecl())
      case _ => throw error(s"Expecting : or :: but ${tokens.head.kind} was found")

  private def kind(): Kind =
    tokens.head match
      case Token.Pi =>
        matchToken(TokenKind.Pi)
        val binder = matchToken(TokenKind.Id).asInstanceOf[Token.Id].name
        matchToken(TokenKind.Colon)
        val binderType = typeDecl()
        matchToken(TokenKind.Dot)
        Kind.Pi(binder, binderType, kind())
      case Token.Product =>
        matchToken(TokenKind.Product)
        Kind.Type
      case _ =>
        matchToken(TokenKind.LeftBracket)
        val lhs = typeDecl()
        matchToken(TokenKind.RightBracket)
        matchToken(TokenKind.RightArrow)
        Kind.Pi("_", lhs, kind())


  private def typeAlias(): SyntaxNode =
    matchToken(TokenKind.Type)
    val name = matchToken(TokenKind.Id).asInstanceOf[Token.Id].name
    matchToken(TokenKind.Equal)
    val t = typeDecl()
    matchToken(TokenKind.Semicolon)
    return SyntaxNode.TypeAlias(name, t)

  private def expr(): SyntaxNode = application()

  private def application(): SyntaxNode =
    val first = letBinding()
    return applicationRest(first)

  private def applicationRest(first: SyntaxNode): SyntaxNode =
    return tokens.headOption match
      case Some(token) if token.isExprStart =>
        val second = letBinding()
        return applicationRest(SyntaxNode.Application(first, second))
      case _ => first

  private def letBinding(): SyntaxNode =
    if tokens.head.kind != TokenKind.Let then
      return ifExpr()
    matchToken(TokenKind.Let)
    val isRec = tokens.head.kind == TokenKind.Rec
    if isRec then matchToken(TokenKind.Rec)
    val binder = matchToken(TokenKind.Id).asInstanceOf[Token.Id].name
    val binderType = tokens.head.kind match
      case TokenKind.Colon =>
        matchToken(TokenKind.Colon)
        Some(typeDecl())
      case _ => None
    matchToken(TokenKind.Equal)
    val binderExpr = expr()
    return tokens.headOption match
      case Some(token) if token.kind == TokenKind.In =>
        matchToken(TokenKind.In)
        val body = expr()
        matchToken(TokenKind.End)
        SyntaxNode.LetBinding(isRec, binder, binderType, binderExpr, Some(body))
      case _ =>
        SyntaxNode.LetBinding(isRec, binder, binderType, binderExpr, None)

  private def ifExpr(): SyntaxNode =
    if tokens.head.kind != TokenKind.If then
      return abstraction()
    matchToken(TokenKind.If)
    val condition = expr()
    matchToken(TokenKind.Then)
    val thenClause = expr()
    matchToken(TokenKind.Else)
    val elseClause = expr()
    return SyntaxNode.If(condition, thenClause, elseClause)

  private def abstraction(): SyntaxNode =
    if tokens.head.kind != TokenKind.Lambda then
      return sequence()
    matchToken(TokenKind.Lambda)
    val binder = matchToken(TokenKind.Id).asInstanceOf[Token.Id].name
    val binderType = if tokens.head.kind == TokenKind.Colon then
      matchToken(TokenKind.Colon)
      Some(typeDecl())
    else
      None
    matchToken(TokenKind.DoubleArrow)
    val body = expr()
    SyntaxNode.Abstraction(binder, binderType, body)

  private def sequence(): SyntaxNode =
    val f = equality()
    return sequenceRest(f)

  private def sequenceRest(first: SyntaxNode): SyntaxNode =
    return tokens.headOption match
      case Some(token) if token.kind == TokenKind.Semicolon =>
        matchToken(TokenKind.Semicolon)
        val second = equality()
        sequenceRest(SyntaxNode.Sequence(first, second))
      case _ => first

  private def equality(): SyntaxNode =
    val f = logical()
    return equalityRest(f)

  private def equalityRest(first: SyntaxNode): SyntaxNode =
    return tokens.headOption match
      case Some(token) if token.kind == TokenKind.EqualEqual =>
        matchToken(TokenKind.EqualEqual)
        val second = logical()
        equalityRest(SyntaxNode.Equal(first, second))
      case Some(token) if token.kind == TokenKind.NotEqual =>
        matchToken(TokenKind.NotEqual)
        val second = logical()
        equalityRest(SyntaxNode.NotEqual(first, second))
      case _ => first

  private def logical(): SyntaxNode =
    val f = comparison()
    return logicalRest(f)

  private def logicalRest(first: SyntaxNode): SyntaxNode =
    return tokens.headOption match
      case Some(token) if token.kind == TokenKind.AmpAmp =>
        matchToken(TokenKind.AmpAmp)
        val second = comparison()
        logicalRest(SyntaxNode.Conjunction(first, second))
      case Some(token) if token.kind == TokenKind.PipePipe =>
        matchToken(TokenKind.PipePipe)
        val second = comparison()
        logicalRest(SyntaxNode.Disjunction(first, second))
      case _ => first

  private def comparison(): SyntaxNode =
    val f = add()
    return comparisonRest(f)

  private def comparisonRest(first: SyntaxNode): SyntaxNode =
    return tokens.headOption match
      case Some(token) if token.kind == TokenKind.LessThan =>
        matchToken(TokenKind.LessThan)
        val second = add()
        comparisonRest(SyntaxNode.LessThan(first, second))
      case Some(token) if token.kind == TokenKind.GreaterThan =>
        matchToken(TokenKind.GreaterThan)
        val second = add()
        comparisonRest(SyntaxNode.GreaterThan(first, second))
      case Some(token) if token.kind == TokenKind.LessThanEqual =>
        matchToken(TokenKind.LessThanEqual)
        val second = add()
        comparisonRest(SyntaxNode.LessThanEqual(first, second))
      case Some(token) if token.kind == TokenKind.GreaterThanEqual =>
        matchToken(TokenKind.GreaterThanEqual)
        val second = add()
        comparisonRest(SyntaxNode.GreaterThanEqual(first, second))
      case _ => first

  private def add(): SyntaxNode =
    val f = mul()
    return addRest(f)

  private def addRest(first: SyntaxNode): SyntaxNode =
    return tokens.headOption match
      case Some(token) if token.kind == TokenKind.Plus =>
        matchToken(TokenKind.Plus)
        val second = mul()
        addRest(SyntaxNode.Addition(first, second))
      case Some(token) if token.kind == TokenKind.Minus =>
        matchToken(TokenKind.Minus)
        val second = mul()
        addRest(SyntaxNode.Subtraction(first, second))
      case _ => first

  private def mul(): SyntaxNode =
    val f = projection()
    return mulRest(f)

  private def mulRest(first: SyntaxNode): SyntaxNode =
    return tokens.headOption match
      case Some(token) if token.kind == TokenKind.Product =>
        matchToken(TokenKind.Product)
        val second = projection()
        mulRest(SyntaxNode.Multiplication(first, second))
      case Some(token) if token.kind == TokenKind.Divides =>
        matchToken(TokenKind.Divides)
        val second = projection()
        mulRest(SyntaxNode.Division(first, second))
      case _ => first

  private def projection(): SyntaxNode =
    val f = factor()
    return projectionRest(f)

  private def projectionRest(first: SyntaxNode): SyntaxNode =
    return tokens.headOption match
      case Some(token) if token.kind == TokenKind.Dot =>
        matchToken(TokenKind.Dot)
        val second = matchToken(TokenKind.Index).asInstanceOf[Token.Index].value
        (tokens.headOption, tokens.tail.headOption) match
          case (Some(token1), Some(token2)) if token1.kind == TokenKind.Dot && token2.kind == TokenKind.Index =>
            projectionRest(SyntaxNode.Projection(first, second.fold(SyntaxNode.Id(_), SyntaxNode.Number(_))))
          case _ => SyntaxNode.Projection(first, second.fold(SyntaxNode.Id(_), SyntaxNode.Number(_)))
      case _ => first

  private def factor(): SyntaxNode =
    return tokens.head.kind match
      case TokenKind.Id =>
        val id = matchToken(TokenKind.Id).asInstanceOf[Token.Id].name
        SyntaxNode.Id(id)
      case TokenKind.LeftParen =>
        if probeTuple() then
          tuple()
        else
          matchToken(TokenKind.LeftParen)
          val result = expr()
          matchToken(TokenKind.RightParen)
          result
      case TokenKind.Number =>
        val number = matchToken(TokenKind.Number).asInstanceOf[Token.Number].value
        SyntaxNode.Number(number)
      case TokenKind.True | TokenKind.False =>
        SyntaxNode.Bool(matchToken(tokens.head.kind).kind == TokenKind.True)
      case TokenKind.Not =>
        matchToken(TokenKind.Not)
        SyntaxNode.Negation(expr())
      case TokenKind.Sharp =>
        matchToken(TokenKind.Sharp)
        val name = matchToken(TokenKind.Id).asInstanceOf[Token.Id].name
        matchToken(TokenKind.LeftParen)
        val arg = expr()
        matchToken(TokenKind.RightParen)
        SyntaxNode.Macro(name, arg)
      case _ =>
        throw IllegalStateException("Expected identifier or left paren but got " + tokens.head.kind)

  private def tuple(): SyntaxNode.Tuple =
    matchToken(TokenKind.LeftParen)
    val first = expr()
    val rest = tupleRest()
    matchToken(TokenKind.RightParen)
    SyntaxNode.Tuple(first :: rest)

  private def tupleRest(): List[SyntaxNode] =
    return tokens.head.kind match
      case TokenKind.Comma =>
        matchToken(TokenKind.Comma)
        val first = expr()
        val rest = tupleRest()
        first :: rest
      case _ => List.empty

  private def probeTuple(): Boolean =
    return tokens.head.kind == TokenKind.LeftParen && tokens(2).kind == TokenKind.Comma

  private def matchTypeAssertion(): (String, TypeDecl) =
    val binderName = matchToken(TokenKind.Id).asInstanceOf[Token.Id].name
    matchToken(TokenKind.Colon)
    val binderType = typeDecl()
    return (binderName, binderType)

  private def typeDecl(): TypeDecl =
    return tokens.head.kind match
      case d@(TokenKind.Pi | TokenKind.Sigma) =>
        matchToken(d)
        val (binderName, binderType) = matchTypeAssertion()
        matchToken(TokenKind.Dot)
        val body = typeDecl()
        if d == TokenKind.Pi then
          TypeDecl.PiType(binderName, binderType, body)
        else
          TypeDecl.SigmaType(binderName, binderType, body)
      case TokenKind.Lambda => typeOperator()
      case TokenKind.Unit =>
        matchToken(TokenKind.Unit)
        TypeDecl.UnitType
      case TokenKind.Bool =>
        matchToken(TokenKind.Bool)
        TypeDecl.BoolType
      case TokenKind.Nat =>
        matchToken(TokenKind.Nat)
        TypeDecl.NatType
      case _ => dependentInstantiation()

  private def typeOperator(): TypeDecl =
    matchToken(TokenKind.Lambda)
    val (binderName, binderType) = matchTypeAssertion()
    matchToken(TokenKind.RightArrow)
    val body = typeDecl()
    return TypeDecl.DependentOperator(binderName, binderType, body)

  private def dependentInstantiation(): TypeDecl =
    val first = functionType()
    if tokens.head.kind != TokenKind.LeftBracket then
      return first
    val args = dependentInstantiationArguments()
    return args.tail.foldLeft(TypeDecl.DependentInstantiation(first, args.head))(TypeDecl.DependentInstantiation(_, _))

  private def dependentInstantiationArguments(): List[SyntaxNode] =
    if tokens.head.kind == TokenKind.LeftBracket then
      matchToken(TokenKind.LeftBracket)
      val first = expr()
      matchToken(TokenKind.RightBracket)
      first :: dependentInstantiationArguments()
    else Nil

  private def functionType(): TypeDecl =
    val first = productType()
    return functionTypeRest(first)

  private def functionTypeRest(first: TypeDecl): TypeDecl =
    return tokens.head.kind match
      case TokenKind.RightArrow =>
        matchToken(TokenKind.RightArrow)
        val second = functionType()
        functionTypeRest(TypeDecl.PiType("_", first, second))
      case _ => first


  private def productType(): TypeDecl =
    val first = typeFactor()
    val rest = productTypeRest()
    return if rest.isEmpty then first else TypeDecl.ProductType(first :: rest)

  private def productTypeRest(): List[TypeDecl] =
    return tokens.head.kind match
      case TokenKind.Product =>
        matchToken(TokenKind.Product)
        val first = typeFactor()
        val rest = productTypeRest()
        first :: rest
      case _ => List.empty

  private def typeFactor(): TypeDecl =
    return tokens.head match
      case Token.Id(name) =>
        matchToken(TokenKind.Id)
        TypeDecl.Var(name)
      case Token.LeftParen =>
        matchToken(TokenKind.LeftParen)
        val result = typeDecl()
        matchToken(TokenKind.RightParen)
        result
      case _ => throw IllegalStateException("Expected identifier or left paren but got " + tokens.head.kind)
end Parser