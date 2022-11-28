package ink.sora

import SyntaxNode.Division

trait Equalizer:
  def kindEquiv(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: Kind, rhs: Kind): Boolean
  def typeEquiv(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: TypeDecl, rhs: TypeDecl): Boolean
  def termEquiv(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode): Boolean

given Equalizer = new BetaEtaEquality()

class BetaEtaEquality extends Equalizer:
  override def kindEquiv(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: Kind, rhs: Kind): Boolean =
    return (lhs, rhs) match
      case Kind.Type -> Kind.Type => true
      case (Kind.Pi(_, lhsBinderType, lhsBody), Kind.Pi(_, rhsBinderType, rhsBody)) =>
        typeEquiv(context, macros, lhsBinderType, rhsBinderType) && kindEquiv(context, macros, lhsBody, rhsBody)
      case _ => false

  override def typeEquiv(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: TypeDecl, rhs: TypeDecl): Boolean =
    def dependentEquiv(lhs: (String, TypeDecl, TypeDecl), rhs: (String, TypeDecl, TypeDecl)): Boolean =
      val (lhsBinder, lhsBinderType, lhsBody) = lhs
      val (rhsBinder, rhsBinderType, rhsBody) = rhs
      val unifiedBinder = ns(fvDep(lhsBody) union fvDep(rhsBody))
      val unifiedLhsBody = substituteDepType(lhsBody, lhsBinder, SyntaxNode.Id(unifiedBinder))
      val unifiedRhsBody = substituteDepType(rhsBody, rhsBinder, SyntaxNode.Id(unifiedBinder))
      val binderTypeEquiv = typeEquiv(context, macros, lhsBinderType, rhsBinderType)
      context.push()
      val bodyTypeEquiv = typeEquiv(context.addTermBinding(unifiedBinder, lhsBinderType), macros, unifiedLhsBody, unifiedRhsBody)
      return (binderTypeEquiv && bodyTypeEquiv).run(_ => context.pop())

    return (lhs, rhs) match
      case (TypeDecl.Var(lhsName), TypeDecl.Var(rhsName)) =>
        val lhsAlias = context.lookupAliasBindingOrDefault(lhsName, lhs)
        val rhsAlias = context.lookupAliasBindingOrDefault(rhsName, rhs)
        if lhsAlias -> rhsAlias != lhs -> rhs then typeEquiv(context, macros, lhsAlias, rhsAlias) else lhsName == rhsName
      case (TypeDecl.Var(lhsName), _) =>
        val alias = context.lookupAliasBindingOrDefault(lhsName, lhs)
        if alias != lhs then typeEquiv(context, macros, alias, rhs) else false
      case (_, TypeDecl.Var(rhsName)) =>
        val alias = context.lookupAliasBindingOrDefault(rhsName, rhs)
        if alias != rhs then typeEquiv(context, macros, lhs, alias) else false
      case (TypeDecl.PiType(lhsBinder, lhsBinderType, lhsBody), TypeDecl.PiType(rhsBinder, rhsBinderType, rhsBody)) =>
        dependentEquiv((lhsBinder, lhsBinderType, lhsBody), (rhsBinder, rhsBinderType, rhsBody))
      case (TypeDecl.SigmaType(lhsBinder, lhsBinderType, lhsBody), TypeDecl.PiType(rhsBinder, rhsBinderType, rhsBody)) =>
        dependentEquiv((lhsBinder, lhsBinderType, lhsBody), (rhsBinder, rhsBinderType, rhsBody))
      case (TypeDecl.DependentOperator(lhsBinder, lhsBinderType, lhsBody), TypeDecl.DependentOperator(rhsBinder, rhsBinderType, rhsBody)) =>
        dependentEquiv((lhsBinder, lhsBinderType, lhsBody), (rhsBinder, rhsBinderType, rhsBody))
      case (TypeDecl.UnitType, TypeDecl.UnitType) | (TypeDecl.BoolType, TypeDecl.BoolType) | (TypeDecl.NatType, TypeDecl.NatType) => true
      case (TypeDecl.ProductType(lhsProducts), TypeDecl.ProductType(rhsProducts)) =>
        lhsProducts.size == rhsProducts.size && lhsProducts.zip(rhsProducts).forall(typeEquiv(context, macros, _, _))
      case (TypeDecl.DependentInstantiation(lhsF, lhsA), TypeDecl.DependentInstantiation(rhsF, rhsA)) =>
        typeEquiv(context, macros, lhsF, rhsF) && termEquiv(context, macros, lhsA, rhsA)
      case _ => false

  override def termEquiv(context: SymbolContext, macros: Map[String, (SyntaxNode, SymbolContext) => Unit], lhs: SyntaxNode, rhs: SyntaxNode): Boolean =
    return (WeakNormalHeadNormalizer.normalize(context, lhs, macros), WeakNormalHeadNormalizer.normalize(context, rhs, macros)) match
      case (SyntaxNode.Id(lhsId), SyntaxNode.Id(rhsId)) => lhsId == rhsId
      case (SyntaxNode.Bool(lhsValue), SyntaxNode.Bool(rhsValue)) => lhsValue == rhsValue
      case (SyntaxNode.Number(lhsValue), SyntaxNode.Number(rhsValue)) => lhsValue == rhsValue
      case (SyntaxNode.Unit, SyntaxNode.Unit) => true
      case (SyntaxNode.Sequence(_, lhsSnd), SyntaxNode.Sequence(_, rhsSnd)) => termEquiv(context, macros, lhsSnd, rhsSnd)
      case (SyntaxNode.Abstraction(lhsBinder, lhsBinderType, lhsBody), SyntaxNode.Abstraction(rhsBinder, rhsBinderType, rhsBody)) =>
        require(lhsBinderType.isDefined) // TODO
        require(rhsBinderType.isDefined)
        val unifiedBinder = ns(fv(lhsBody) union fv(rhsBody))
        val unifiedLhsBody = substituteTerm(lhsBody, lhsBinder, SyntaxNode.Id(unifiedBinder))
        val unifiedRhsBody = substituteTerm(rhsBody, rhsBinder, SyntaxNode.Id(unifiedBinder))
        typeEquiv(context, macros, lhsBinderType.get, rhsBinderType.get) &&
          termEquiv(context.addTermBinding(unifiedBinder, lhsBinderType.get), macros, unifiedLhsBody, unifiedRhsBody)
      case (BinOp(binOpLhs), BinOp(binOpRhs)) => termEquiv(context, macros, binOpLhs.lhs, binOpRhs.lhs) && termEquiv(context, macros, binOpLhs.rhs, binOpRhs.rhs)
      case (SyntaxNode.Macro(_, _), SyntaxNode.Macro(_, _)) => true