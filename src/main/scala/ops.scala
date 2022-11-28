package ink.sora

import scala.annotation.{tailrec, targetName, unused}
import scala.reflect.ClassTag
import scala.util.Try

extension [T](x: Try[T])
  @targetName("bind")
  def >>=[V](f: T => Try[V]): Try[V] = x.flatMap(f)

extension [T](x: T)
  def run(f: T => Unit): T =
    f(x)
    x

extension [T](e: Iterable[T])
  def ofType[U: ClassTag]: Iterable[U] =
    e.collect { case x: U => x }
  def search[U](f: U => Boolean)(using T =:= Iterable[U]): Option[U] =
    e.asInstanceOf[Iterable[Iterable[U]]].flatMap(_.find(f)).headOption

val ns = names()

private def names(): Set[String] => String =
  var i = 0
  @tailrec
  def gen(excludes: Set[String]): String =
    val candidate = s"x$i"
    i += 1
    if excludes.contains(candidate) then gen(excludes) else candidate
  return gen

def error(message: => String): Exception =
  new IllegalStateException(message)

def substituteTerm(term: SyntaxNode, target: String, replacement: SyntaxNode): SyntaxNode =
  return term match
    case lb@SyntaxNode.LetBinding(_, binder, _, binderExpr, body) =>
      if binder == target then term
      else body match
        case None => lb.copy(binderExpr = substituteTerm(binderExpr, target, replacement))
        case Some(b) =>
          if fv(replacement) contains binder then
            val newLet = alphaConv(term, replacement)
            substituteTerm(newLet, target, replacement)
          else
            lb.copy(binderExpr = substituteTerm(binderExpr, target, replacement), body = Some(substituteTerm(b, target, replacement)))
    case SyntaxNode.Application(f, a) => SyntaxNode.Application(substituteTerm(f, target, replacement), substituteTerm(a, target, replacement))
    case SyntaxNode.Abstraction(binder, binderType, body) =>
      if binder == target then term
      else if fv(replacement) contains binder then
        val newAbs = alphaConv(term, replacement)
        substituteTerm(newAbs, target, replacement)
      else SyntaxNode.Abstraction(binder, binderType, substituteTerm(body, target, replacement))
    case SyntaxNode.Id(name) => if name == target then replacement else term
    case SyntaxNode.Number(_) | SyntaxNode.Bool(_) | SyntaxNode.Unit => term
    case SyntaxNode.Tuple(products) => SyntaxNode.Tuple(products.map(substituteTerm(_, target, replacement)))
    case SyntaxNode.If(cond, thenClause, elseClause) =>
      SyntaxNode.If(
        substituteTerm(cond, target, replacement),
        substituteTerm(thenClause, target, replacement),
        substituteTerm(elseClause, target, replacement))
    case SyntaxNode.Fixpoint(subject) => SyntaxNode.Fixpoint(substituteTerm(subject, target, replacement))
    case BinOp(t) => t.run { bo =>
      bo.lhs = substituteTerm(t.lhs, target, replacement)
      bo.rhs = substituteTerm(t.rhs, target, replacement)
    }
    case UnOp(t) => t.run(uo => uo.subject = substituteTerm(uo.subject, target, replacement))
    case _ => throw new IllegalStateException("Unknown term")

def substituteDepType(ty: TypeDecl, target: String, replacement: SyntaxNode): TypeDecl =
  return ty match
    case TypeDecl.UnitType | TypeDecl.BoolType | TypeDecl.NatType => ty
    case TypeDecl.PiType(binder, binderType, body) =>
      if binder == target then ty
      else if fv(replacement) contains binder then
        val newType = alphaConv(ty, replacement)
        substituteDepType(newType, target, replacement)
      else TypeDecl.PiType(binder, binderType, substituteDepType(body, target, replacement))
    case TypeDecl.SigmaType(binder, binderType, body) =>
      if binder == target then ty
      else if fv(replacement) contains binder then
        val newType = alphaConv(ty, replacement)
        substituteDepType(newType, target, replacement)
      else TypeDecl.SigmaType(binder, binderType, substituteDepType(body, target, replacement))
    case TypeDecl.ProductType(products) => TypeDecl.ProductType(products.map(substituteDepType(_, target, replacement)))
    case TypeDecl.DependentOperator(binder, binderType, body) =>
      if binder == target then ty
      else if fv(replacement) contains binder then
        val newType = alphaConv(ty, replacement)
        substituteDepType(newType, target, replacement)
      else TypeDecl.DependentOperator(binder, binderType, substituteDepType(body, target, replacement))
    case TypeDecl.Var(name) => if name == target then ty else TypeDecl.Var(name)
    case TypeDecl.DependentInstantiation(f, a) =>
      TypeDecl.DependentInstantiation(substituteDepType(f, target, replacement), substituteTerm(a, target, replacement))

def alphaConv(ty: TypeDecl, capture: SyntaxNode): TypeDecl =
  def substitute(binder: String, body: TypeDecl): (String, TypeDecl) =
    val newBinder = ns(fv(capture) union fvDep(body))
    val newBody = substituteDepType(body, binder, SyntaxNode.Id(newBinder))
    return (newBinder, newBody)
  return ty match
    case TypeDecl.PiType(binder, binderType, body) =>
      val (newBinder, newBody) = substitute(binder, body)
      TypeDecl.PiType(newBinder, binderType, newBody)
    case TypeDecl.SigmaType(binder, binderType, body) =>
      val (newBinder, newBody) = substitute(binder, body)
      TypeDecl.SigmaType(newBinder, binderType, newBody)
    case TypeDecl.DependentOperator(binder, binderType, body) =>
      val (newBinder, newBody) = substitute(binder, body)
      TypeDecl.DependentOperator(newBinder, binderType, newBody)
    case _ => ty

def alphaConv(term: SyntaxNode, capture: SyntaxNode): SyntaxNode =
  def substitute(binder: String, body: SyntaxNode): (String, SyntaxNode) =
    val newBinder = ns(fv(capture) union fv(body))
    val newBody = substituteTerm(body, binder, SyntaxNode.Id(newBinder))
    return (newBinder, newBody)
  return term match
    case SyntaxNode.Abstraction(binder, binderType, body) =>
      val (newBinder, newBody) = substitute(binder, body)
      SyntaxNode.Abstraction(newBinder, binderType, newBody)
    case lb@SyntaxNode.LetBinding(_, binder, _, _, Some(body)) =>
      val (newBinder, newBody) = substitute(binder, body)
      lb.copy(binder = newBinder, body = Some(newBody))
    case _ => term

private def fvDep(ty: TypeDecl): Set[String] =
  ty match
    case TypeDecl.UnitType | TypeDecl.BoolType | TypeDecl.NatType => Set.empty
    case TypeDecl.PiType(binder, _, body) => fvDep(body).filter(_ != binder)
    case TypeDecl.SigmaType(binder, _, body) => fvDep(body).filter(_ != binder)
    case TypeDecl.ProductType(products) => products.flatMap(fvDep).toSet
    case TypeDecl.DependentOperator(binder, _, body) => fvDep(body).filter(_ != binder)
    case TypeDecl.Var(name) => Set(name)
    case TypeDecl.DependentInstantiation(f, a) => fvDep(f) union fv(a)

private def fv(term: SyntaxNode): Set[String] =
  term match
    case SyntaxNode.LetBinding(_, binder, _, binderExpr, body) =>
      val bodyFv = if body.isDefined then
        fv(body.get).filter(_ != binder)
      else Set.empty
      fv(binderExpr) union bodyFv
    case SyntaxNode.Application(f, a) => fv(f) union fv(a)
    case SyntaxNode.Abstraction(binder, _, body) => fv(body).filter(_ != binder)
    case SyntaxNode.Tuple(products) => products.flatMap(fv).toSet
    case SyntaxNode.If(cond, thenClause, elseClause) => fv(cond) union fv(thenClause) union fv(elseClause)
    case SyntaxNode.Id(name) => Set(name)
    case BinOp(t) => fv(t.lhs) union fv(t.rhs)
    case UnOp(t) => fv(t.subject)
    case _ => Set.empty