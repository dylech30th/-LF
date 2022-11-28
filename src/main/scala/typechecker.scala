package ink.sora

import scala.annotation.tailrec
import scala.util.{Failure, Success, Try}

// A type checker for Edinburgh Logical Framework, a first-order dependently-typed lambda calculus

enum Kind:
  case Type
  case Pi(binder: String, binderType: TypeDecl, bodyKind: Kind)
end Kind

def kindOf(context: SymbolContext, decl: TypeDecl, macros: Map[String, (SyntaxNode, SymbolContext) => Unit]): Try[Kind] =
  return decl match
    case TypeDecl.Var(name) =>
      context.lookupFirstTypeBinding { case TypeDecl.Var(n) => name == n } match
        case Some(kind) => if checkKind(context, kind, macros) then Success(kind) else Failure(error(s"Kind error: $kind for $name"))
        case None => Failure(new IllegalStateException("Type is not found in context"))
    case t@(TypeDecl.PiType(_, _, _) | TypeDecl.SigmaType(_, _, _)) =>
      val (binder, binderType, body) = (t.productElement(0).asInstanceOf[String], t.productElement(1).asInstanceOf[TypeDecl], t.productElement(2).asInstanceOf[TypeDecl])
      kindOf(context.addTermBinding(binder, binderType), body, macros)
        .flatMap(k => if k == Kind.Type then Success(Kind.Type) else Failure(error("Kind of body type is not *")))
    case TypeDecl.DependentOperator(binder, binderType, body) =>
      kindOf(context.addTermBinding(binder, binderType), body, macros)
        .map(Kind.Pi(binder, binderType, _))
    case TypeDecl.DependentInstantiation(f, a) =>
      for
        case Kind.Pi(_, binderType, bodyKind) <- kindOf(context, f, macros)
        ty <- typeOf(context, a, macros)
        result <- mapTypeEquiv(s"Type mismatch in dependent instantiation while instantiating $f with $a", context, macros, Success(binderType), ty)
          .map(_ => bodyKind)
      yield result
    case TypeDecl.ProductType(_) | TypeDecl.BoolType | TypeDecl.UnitType | TypeDecl.NatType => Success(Kind.Type)

def typeOfUnwrapped(context: SymbolContext, term: SyntaxNode, macros: Map[String, (SyntaxNode, SymbolContext) => Unit]): TypeDecl =
  typeOf(context, term, macros).get

def typeOf(context: SymbolContext, term: SyntaxNode, macros: Map[String, (SyntaxNode, SymbolContext) => Unit])(using Equalizer): Try[TypeDecl] =
  return term match
    case SyntaxNode.Id(name) =>
      context.lookupTermBinding(name) match
        case Some(ty) => Success(ty)
        case None => Failure(new IllegalStateException(s"Term $name is not found in context"))
    case SyntaxNode.LetBinding(_, binder, binderType, binderExpr, body) =>
      (body, binderType) match
        case (Some(b), Some(typ)) => // if binder's type is marked explicitly
          context.push()
          mapTypeEquiv("Type mismatch in the binder of let", context, macros, typeOf(context, binderExpr, macros), typ)
            .flatMap(_ => typeOf(context.addTermBinding(binder, typ), b, macros).run(_ => context.pop()))
        case (Some(b), None) => // if binder's type is not marked
          context.push()
          typeOf(context, binderExpr, macros).flatMap(ty => typeOf(context.addTermBinding(binder, ty), b, macros).run(_ => context.pop()))
        case (None, Some(typ)) =>
          mapTypeEquiv("Type mismatch in the binder of let", context, macros, typeOf(context, binderExpr, macros), typ)
            .map(_ => typ)
        case (None, None) =>
          typeOf(context, binderExpr, macros).map(_ => TypeDecl.UnitType)
    case SyntaxNode.Application(f, a) =>
      for
        case TypeDecl.PiType(binderName, binderType, body) <- typeOf(context, f, macros)
        ty <- typeOf(context, a, macros)
        result <- mapTypeEquiv(s"Type mismatch while applying $a to $f", context, macros, Success(binderType), ty)
          .map(_ => substituteDepType(body, binderName, a))
      yield result
    case SyntaxNode.Abstraction(binderName, binderType, body) =>
      require(binderType.isDefined) // TODO
      context.push()
      val bodyType = typeOf(context.addTermBinding(binderName, binderType.get), body, macros)
      bodyType.map(t => TypeDecl.PiType(binderName, binderType.get, t)).run(_ => context.pop())
    case SyntaxNode.Number(_) => Success(TypeDecl.NatType)
    case SyntaxNode.Bool(_) => Success(TypeDecl.BoolType)
    case SyntaxNode.Unit => Success(TypeDecl.UnitType)
    case SyntaxNode.Tuple(products) =>
      val types = products.map(typeOf(context, _, macros))
      if types.forall(_.isSuccess) then
        Success(TypeDecl.ProductType(types.map(_.get)))
      else
        types.find(_.isFailure).get
    case SyntaxNode.If(cond, thenClause, elseClause) =>
      if typeOf(context, cond, macros) == TypeDecl.BoolType then
        context.push()
        val thenType = typeOf(context, thenClause, macros)
        context.pop()
        context.push()
        val elseType = typeOf(context, elseClause, macros)
        context.pop()
        if thenType == elseType then
          thenType
        else
          Failure(new IllegalStateException("If-then-else branches must have the same type"))
      else
        Failure(new IllegalStateException("If condition must be a boolean"))
    case SyntaxNode.Sequence(first, second) =>
      typeOf(context, first, macros).flatMap(_ => typeOf(context, second, macros))
    case t@(SyntaxNode.Addition(_, _)
            | SyntaxNode.Subtraction(_, _)
            | SyntaxNode.Multiplication(_, _)
            | SyntaxNode.Division(_, _)
            | SyntaxNode.LessThan(_, _)
            | SyntaxNode.LessThanEqual(_, _)
            | SyntaxNode.GreaterThan(_, _)
            | SyntaxNode.GreaterThanEqual(_, _)) =>
      val (lhs, rhs) = (t.productElement(0).asInstanceOf[SyntaxNode], t.productElement(1).asInstanceOf[SyntaxNode])
      mapTypeEquivSeq("Arithmetic and comparison operators must be applied to numbers", context, macros, TypeDecl.NatType, typeOf(context, lhs, macros), typeOf(context, rhs, macros))
        .map(_ => TypeDecl.NatType)
    case SyntaxNode.Equal(lhs, rhs) =>
      typeOf(context, rhs, macros)
        .flatMap(mapTypeEquiv("Equality must be applied to terms of the same type", context, macros, typeOf(context, lhs, macros), _))
        .map(_ => TypeDecl.BoolType)
    case t@(SyntaxNode.Conjunction(_, _) | SyntaxNode.Disjunction(_, _)) =>
      val (lhs, rhs) = (t.productElement(0).asInstanceOf[SyntaxNode], t.productElement(1).asInstanceOf[SyntaxNode])
      mapTypeEquivSeq("Logical operators must be applied to booleans", context, macros, TypeDecl.BoolType, typeOf(context, lhs, macros), typeOf(context, rhs, macros))
        .map(_ => TypeDecl.BoolType)
    case SyntaxNode.Negation(term) =>
      mapTypeEquiv("Logical operators must be applied to booleans", context, macros, typeOf(context, term, macros), TypeDecl.BoolType)
        .map(_ => TypeDecl.BoolType)
    case SyntaxNode.TypeDefine(ne, kind) =>
      context.addTypeBinding(TypeDecl.Var(ne), kind)
      Success(TypeDecl.UnitType)
    case SyntaxNode.TermDefine(ne, ty) =>
      context.addTermBinding(ne, ty)
      Success(TypeDecl.UnitType)
    case SyntaxNode.Macro(_, target) =>
      typeOf(context, target, macros)
      Success(TypeDecl.UnitType)
    case t => Failure(new IllegalStateException(s"Unknown term: ${pprint(t)}"))

def typeOf(context: SymbolContext, terms: List[SyntaxNode], macros: Map[String, (SyntaxNode, SymbolContext) => Unit])(using Equalizer): Try[TypeDecl] =
  terms.foldLeft(Success(TypeDecl.UnitType): Try[TypeDecl])((acc, term) => acc.flatMap(_ => typeOf(context, term, macros)))

private def checkKind(context: SymbolContext, kind: Kind, macros: Map[String, (SyntaxNode, SymbolContext) => Unit]): Boolean =
  return kind match
    case Kind.Type => true
    // Kind for dependent type operator
    case Kind.Pi(_, binderType, bodyKind) =>
      kindOf(context, binderType, macros).isSuccess && checkKind(context.addTypeBinding(binderType, Kind.Type), bodyKind, macros)

private def mapTypeEquiv(message: => String, context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], ty: Try[TypeDecl], dest: TypeDecl)(using eq: Equalizer): Try[Unit] =
  ty.flatMap(t => if eq.typeEquiv(context, macros, t, dest) then Success(()) else Failure(new IllegalStateException(message)))

private def mapTypeEquivSeq(message: => String, context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], dest: TypeDecl, ts: Try[TypeDecl]*): Try[Unit] =
  ts.foldLeft(Success(()): Try[Unit])((acc, t) => acc.flatMap(_ => mapTypeEquiv(message, context, macros, t, dest)))