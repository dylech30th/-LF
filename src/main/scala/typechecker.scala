package ink.sora

import scala.annotation.tailrec
import scala.util.{Failure, Success, Try}

// A type checker for Edinburgh Logical Framework, a first-order dependently-typed lambda calculus

enum Kind:
  case Type
  case Pi(binder: String, binderType: TypeDecl, bodyKind: Kind)
end Kind

def kindOf(context: SymbolContext, decl: TypeDecl): Try[Kind] =
  return decl match
    case TypeDecl.Var(name) =>
      context.lookupFirstTypeBinding { case TypeDecl.Var(n) => name == n } match
        case Some(kind) => if checkKind(context, kind) then Success(kind) else Failure(error(s"Kind error: $kind for $name"))
        case None => Failure(new IllegalStateException("Type is not found in context"))
    case t@(TypeDecl.PiType(_, _, _) | TypeDecl.SigmaType(_, _, _)) =>
      val (binder, binderType, body) = (t.productElement(0).asInstanceOf[String], t.productElement(1).asInstanceOf[TypeDecl], t.productElement(2).asInstanceOf[TypeDecl])
      kindOf(context.addTermBinding(binder, binderType), body)
        .flatMap(k => if k == Kind.Type then Success(Kind.Type) else Failure(error("Kind of body type is not *")))
    case TypeDecl.DependentOperator(binder, binderType, body) =>
      kindOf(context.addTermBinding(binder, binderType), body)
        .map(Kind.Pi(binder, binderType, _))
    case TypeDecl.DependentInstantiation(f, a) =>
      for
        case Kind.Pi(_, binderType, bodyKind) <- kindOf(context, f)
        ty <- typeOf(context, a)
        result <- mapTypeEquiv(s"Type mismatch in dependent instantiation while instantiating $f with $a", Success(binderType), ty)
          .map(_ => bodyKind)
      yield result
    case TypeDecl.ProductType(_) | TypeDecl.BoolType | TypeDecl.UnitType | TypeDecl.NatType => Success(Kind.Type)

def kindEquiv(lhs: Kind, rhs: Kind): Boolean = true

def typeEquiv(lhs: TypeDecl, rhs: TypeDecl): Boolean = true

def typeOfUnwrapped(context: SymbolContext, term: SyntaxNode): TypeDecl =
  typeOf(context, term).get

def typeOf(context: SymbolContext, term: SyntaxNode): Try[TypeDecl] =
  return term match
    case SyntaxNode.Id(name) =>
      context.lookupTermBinding(name) match
        case Some(ty) => Success(ty)
        case None => Failure(new IllegalStateException("Term is not found in context"))
    case SyntaxNode.LetBinding(_, binder, binderType, binderExpr, body) =>
      (body, binderType) match
        case (Some(b), Some(typ)) => // if binder's type is marked explicitly
          context.push()
          mapTypeEquiv("Type mismatch in the binder of let", typeOf(context, binderExpr), typ)
            .flatMap(_ => typeOf(context.addTermBinding(binder, typ), b).run(_ => context.pop()))
        case (Some(b), None) => // if binder's type is not marked
          context.push()
          typeOf(context, binderExpr).flatMap(ty => typeOf(context.addTermBinding(binder, ty), b).run(_ => context.pop()))
        case (None, Some(typ)) =>
          mapTypeEquiv("Type mismatch in the binder of let", typeOf(context, binderExpr), typ)
            .map(_ => typ)
        case (None, None) =>
          typeOf(context, binderExpr).map(_ => TypeDecl.UnitType)
    case SyntaxNode.Application(f, a) =>
      for
        case TypeDecl.PiType(binderName, binderType, body) <- typeOf(context, f)
        ty <- typeOf(context, a)
        result <- mapTypeEquiv(s"Type mismatch while applying $a to $f", Success(binderType), ty)
          .map(_ => substituteDepType(body, binderName, a))
      yield result
    case SyntaxNode.Abstraction(binderName, binderType, body) =>
      require(binderType.isDefined) // TODO
      context.push()
      val bodyType = typeOf(context.addTermBinding(binderName, binderType.get), body)
      bodyType.map(t => TypeDecl.PiType(binderName, binderType.get, t)).run(_ => context.pop())
    case SyntaxNode.Number(_) => Success(TypeDecl.NatType)
    case SyntaxNode.Bool(_) => Success(TypeDecl.BoolType)
    case SyntaxNode.Unit => Success(TypeDecl.UnitType)
    case SyntaxNode.Tuple(products) =>
      val types = products.map(typeOf(context, _))
      if types.forall(_.isSuccess) then
        Success(TypeDecl.ProductType(types.map(_.get)))
      else
        types.find(_.isFailure).get
    case SyntaxNode.If(cond, thenClause, elseClause) =>
      if typeOf(context, cond) == TypeDecl.BoolType then
        context.push()
        val thenType = typeOf(context, thenClause)
        context.pop()
        context.push()
        val elseType = typeOf(context, elseClause)
        context.pop()
        if thenType == elseType then
          thenType
        else
          Failure(new IllegalStateException("If-then-else branches must have the same type"))
      else
        Failure(new IllegalStateException("If condition must be a boolean"))
    case SyntaxNode.Sequence(first, second) =>
      typeOf(context, first).flatMap(_ => typeOf(context, second))
    case t@(SyntaxNode.Addition(_, _)
            | SyntaxNode.Subtraction(_, _)
            | SyntaxNode.Multiplication(_, _)
            | SyntaxNode.Division(_, _)
            | SyntaxNode.LessThan(_, _)
            | SyntaxNode.LessThanEqual(_, _)
            | SyntaxNode.GreaterThan(_, _)
            | SyntaxNode.GreaterThanEqual(_, _)) =>
      val (lhs, rhs) = (t.productElement(0).asInstanceOf[SyntaxNode], t.productElement(1).asInstanceOf[SyntaxNode])
      mapTypeEquivSeq("Arithmetic and comparison operators must be applied to numbers", TypeDecl.NatType, typeOf(context, lhs), typeOf(context, rhs))
        .map(_ => TypeDecl.NatType)
    case SyntaxNode.Equal(lhs, rhs) =>
      typeOf(context, rhs)
        .flatMap(mapTypeEquiv("Equality must be applied to terms of the same type", typeOf(context, lhs), _))
        .map(_ => TypeDecl.BoolType)
    case t@(SyntaxNode.Conjunction(_, _) | SyntaxNode.Disjunction(_, _)) =>
      val (lhs, rhs) = (t.productElement(0).asInstanceOf[SyntaxNode], t.productElement(1).asInstanceOf[SyntaxNode])
      mapTypeEquivSeq("Logical operators must be applied to booleans", TypeDecl.BoolType, typeOf(context, lhs), typeOf(context, rhs))
        .map(_ => TypeDecl.BoolType)
    case SyntaxNode.Negation(term) =>
      mapTypeEquiv("Logical operators must be applied to booleans", typeOf(context, term), TypeDecl.BoolType)
        .map(_ => TypeDecl.BoolType)
    case _ => Failure(new IllegalStateException("Unknown term"))

private def checkKind(context: SymbolContext, kind: Kind): Boolean =
  return kind match
    case Kind.Type => true
    // Kind for dependent type operator
    case Kind.Pi(_, binderType, bodyKind) =>
      kindOf(context, binderType).isSuccess && checkKind(context.addTypeBinding(binderType, Kind.Type), bodyKind)

private def mapTypeEquiv(message: => String, ty: Try[TypeDecl], dest: TypeDecl): Try[Unit] =
  ty.flatMap(t => if typeEquiv(t, dest) then Success(()) else Failure(new IllegalStateException(message)))

private def mapTypeEquivSeq(message: => String, dest: TypeDecl, ts: Try[TypeDecl]*): Try[Unit] =
  ts.foldLeft(Success(()): Try[Unit])((acc, t) => acc.flatMap(_ => mapTypeEquiv(message, t, dest)))