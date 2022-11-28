package ink.sora

import SyntaxNode.Division

trait Equalizer:
  def kindEquiv(context: SymbolContext, lhs: Kind, rhs: Kind): Boolean
  def typeEquiv(context: SymbolContext, lhs: TypeDecl, rhs: TypeDecl): Boolean
  def termEquiv(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode): Boolean

given Equalizer = new BetaEtaEquality()

class BetaEtaEquality extends Equalizer:
  override def kindEquiv(context: SymbolContext, lhs: Kind, rhs: Kind): Boolean =
    return (lhs, rhs) match
      case Kind.Type -> Kind.Type => true
      case (Kind.Pi(_, lhsBinderType, lhsBody), Kind.Pi(_, rhsBinderType, rhsBody)) =>
        typeEquiv(context, lhsBinderType, rhsBinderType) && kindEquiv(context, lhsBody, rhsBody)
      case _ => false

  override def typeEquiv(context: SymbolContext, lhs: TypeDecl, rhs: TypeDecl): Boolean =
    def dependentEquiv(lhs: (String, TypeDecl, TypeDecl), rhs: (String, TypeDecl, TypeDecl)): Boolean =
      val (lhsBinder, lhsBinderType, lhsBody) = lhs
      val (rhsBinder, rhsBinderType, rhsBody) = rhs
      val unifiedBinder = ns(fvDep(lhsBody) union fvDep(rhsBody))
      val unifiedLhsBody = substituteDepType(lhsBody, lhsBinder, SyntaxNode.Id(unifiedBinder))
      val unifiedRhsBody = substituteDepType(rhsBody, rhsBinder, SyntaxNode.Id(unifiedBinder))
      val binderTypeEquiv = typeEquiv(context, lhsBinderType, rhsBinderType)
      context.push()
      val bodyTypeEquiv = typeEquiv(context.addTermBinding(unifiedBinder, lhsBinderType), unifiedLhsBody, unifiedRhsBody)
      return (binderTypeEquiv && bodyTypeEquiv).run(_ => context.pop())

    return (lhs, rhs) match
      case (TypeDecl.Var(lhsName), TypeDecl.Var(rhsName)) =>
        val lhsAlias = context.lookupAliasBindingOrDefault(lhsName, lhs)
        val rhsAlias = context.lookupAliasBindingOrDefault(rhsName, rhs)
        if lhsAlias -> rhsAlias != lhs -> rhs then typeEquiv(context, lhsAlias, rhsAlias) else lhsName == rhsName
      case (TypeDecl.Var(lhsName), _) =>
        val alias = context.lookupAliasBindingOrDefault(lhsName, lhs)
        if alias != lhs then typeEquiv(context, alias, rhs) else false
      case (_, TypeDecl.Var(rhsName)) =>
        val alias = context.lookupAliasBindingOrDefault(rhsName, rhs)
        if alias != rhs then typeEquiv(context, lhs, alias) else false
      case (TypeDecl.PiType(lhsBinder, lhsBinderType, lhsBody), TypeDecl.PiType(rhsBinder, rhsBinderType, rhsBody)) =>
        dependentEquiv((lhsBinder, lhsBinderType, lhsBody), (rhsBinder, rhsBinderType, rhsBody))
      case (TypeDecl.SigmaType(lhsBinder, lhsBinderType, lhsBody), TypeDecl.PiType(rhsBinder, rhsBinderType, rhsBody)) =>
        dependentEquiv((lhsBinder, lhsBinderType, lhsBody), (rhsBinder, rhsBinderType, rhsBody))
      case (TypeDecl.DependentOperator(lhsBinder, lhsBinderType, lhsBody), TypeDecl.DependentOperator(rhsBinder, rhsBinderType, rhsBody)) =>
        dependentEquiv((lhsBinder, lhsBinderType, lhsBody), (rhsBinder, rhsBinderType, rhsBody))
      case (TypeDecl.UnitType, TypeDecl.UnitType) | (TypeDecl.BoolType, TypeDecl.BoolType) | (TypeDecl.NatType, TypeDecl.NatType) => true
      case (TypeDecl.ProductType(lhsProducts), TypeDecl.ProductType(rhsProducts)) =>
        lhsProducts.size == rhsProducts.size && lhsProducts.zip(rhsProducts).forall(typeEquiv(context, _, _))
      case (TypeDecl.DependentInstantiation(lhsF, lhsA), TypeDecl.DependentInstantiation(rhsF, rhsA)) =>
        typeEquiv(context, lhsF, rhsF) && termEquiv(context, lhsA, rhsA)
      case _ => false

  override def termEquiv(context: SymbolContext, lhs: SyntaxNode, rhs: SyntaxNode): Boolean =
    return (lhs, rhs) match
      case (SyntaxNode.Id(lhsId), SyntaxNode.Id(rhsId)) => lhsId == rhsId
      case (SyntaxNode.Bool(lhsValue), SyntaxNode.Bool(rhsValue)) => lhsValue == rhsValue
      case (SyntaxNode.Number(lhsValue), SyntaxNode.Number(rhsValue)) => lhsValue == rhsValue
      case (SyntaxNode.Unit, SyntaxNode.Unit) => true
      case (SyntaxNode.Sequence(_, lhsSnd), SyntaxNode.Sequence(_, rhsSnd)) => termEquiv(context, lhsSnd, rhsSnd)
      case (SyntaxNode.Abstraction(lhsBinder, lhsBinderType, lhsBody), SyntaxNode.Abstraction(rhsBinder, rhsBinderType, rhsBody)) =>
        require(lhsBinderType.isDefined) // TODO
        require(rhsBinderType.isDefined)
        val unifiedBinder = ns(fv(lhsBody) union fv(rhsBody))
        val unifiedLhsBody = substituteTerm(lhsBody, lhsBinder, SyntaxNode.Id(unifiedBinder))
        val unifiedRhsBody = substituteTerm(rhsBody, rhsBinder, SyntaxNode.Id(unifiedBinder))
        typeEquiv(context, lhsBinderType.get, rhsBinderType.get) &&
          termEquiv(context.addTermBinding(unifiedBinder, lhsBinderType.get), unifiedLhsBody, unifiedRhsBody)
      case (SyntaxNode.Application(lhsF, lhsA), SyntaxNode.Application(rhsF, rhsA)) =>
        termEquiv(context, lhsF, rhsF) && termEquiv(context, lhsA, rhsA)