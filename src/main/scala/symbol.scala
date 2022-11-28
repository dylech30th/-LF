package ink.sora

enum SymbolBinding:
  case TypeBinding(ty: TypeDecl, kind: Kind)
  case TermBinding(name: String, ty: TypeDecl)
  case AssignBinding(name: String, value: SyntaxNode)
  case AliasBinding(name: String, ty: TypeDecl)
end SymbolBinding

class SymbolContext:
  private var symbols: List[Set[SymbolBinding]] = Nil

  def addSymbol(symbol: SymbolBinding): SymbolContext =
    symbols = symbols match
      case Nil => List(Set(symbol))
      case head :: tail => (head + symbol) :: tail
    return this

  def addTypeBinding(ty: TypeDecl, kind: Kind): SymbolContext =
    addSymbol(SymbolBinding.TypeBinding(ty, kind))

  def addTermBinding(name: String, ty: TypeDecl): SymbolContext =
    if name != "_" then
      lookupTermBinding(name).fold(addSymbol(SymbolBinding.TermBinding(name, ty)))(_ => throw error(s"$name is already defined"))
    else this

  def addAssignBinding(name: String, value: SyntaxNode): SymbolContext =
    lookupAssignBinding(name).fold(addSymbol(SymbolBinding.AssignBinding(name, value)))(_ => throw error(s"$name is already defined"))

  def addAliasBinding(name: String, ty: TypeDecl): SymbolContext =
    lookupAliasBinding(name).fold(addSymbol(SymbolBinding.AliasBinding(name, ty)))(_ => throw error(s"$name is already defined"))

  def push(): Unit = symbols = Set.empty :: symbols

  def pop(): Unit = symbols = symbols match
    case Nil => throw new IllegalStateException("Cannot pop from empty context")
    case _ :: tail => tail

  def lookupTypeBinding(ty: TypeDecl): Option[Kind] =
    symbols.map(_.ofType[SymbolBinding.TypeBinding]).search[SymbolBinding.TypeBinding](tb => tb.ty == ty).map(_.kind)

  def lookupTermBinding(name: String): Option[TypeDecl] =
    symbols.map(_.ofType[SymbolBinding.TermBinding]).search[SymbolBinding.TermBinding](_.name == name).map(_.ty)

  def lookupAliasBinding(name: String): Option[TypeDecl] =
    symbols.map(_.ofType[SymbolBinding.AliasBinding]).search[SymbolBinding.AliasBinding](_.name == name).map(_.ty)
  
  def lookupAliasBindingOrDefault(name: String, default: => TypeDecl): TypeDecl =
    lookupAliasBinding(name).getOrElse(default)

  def lookupAssignBinding(name: String): Option[SyntaxNode] =
    symbols.map(_.ofType[SymbolBinding.AssignBinding]).search[SymbolBinding.AssignBinding](_.name == name).map(_.value)

  def lookupFirstTypeBinding(pred: PartialFunction[TypeDecl, Boolean]): Option[Kind] =
    symbols.map(_.ofType[SymbolBinding.TypeBinding]).search[SymbolBinding.TypeBinding](t => pred(t.ty)).map(_.kind)
end SymbolContext