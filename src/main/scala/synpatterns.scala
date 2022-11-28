package ink.sora

object BinOp:
  def unapply(arg: SyntaxNode): Option[SyntaxNode & BinaryOperator] =
    arg match
      case operator: BinaryOperator => Some(operator)
      case _ => None

object UnOp:
  def unapply(arg: SyntaxNode): Option[SyntaxNode & UnaryOperator] =
    if arg.isInstanceOf[UnaryOperator] then
      Some(arg.asInstanceOf[SyntaxNode & UnaryOperator])
    else None

object SingletonNode:
  def unapply(arg: SyntaxNode): Option[SyntaxNode] =
    arg match
      case SyntaxNode.Unit => Some(SyntaxNode.Unit)
      case SyntaxNode.Bool(_) => Some(arg)
      case SyntaxNode.Number(_) => Some(arg)
      case SyntaxNode.Id(_) => Some(arg)
      case _ => None
      
object NotSingletonNode:
  def unapply(arg: SyntaxNode): Option[SyntaxNode] =
    arg match
      case SingletonNode(_) => None
      case _ => Some(arg)
      
object BinOpLeftNotSingleton:
  def unapply(binOp: BinaryOperator): Option[SyntaxNode] =
    binOp.lhs match
      case NotSingletonNode(n) => Some(n)
      case _ => None
      
object BinOpRightNotSingleton:
  def unapply(binOp: BinaryOperator): Option[SyntaxNode] =
    binOp.rhs match
      case NotSingletonNode(n) => Some(n)
      case _ => None