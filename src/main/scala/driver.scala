package ink.sora

@main
def main(): Unit =
  for tokens <- Lexer(
    """
       define Vector :: [nat] -> *
       define Element :: *
       define newVec: Πn: nat. Vector [n]
       define e: Element
       let first = (λn: nat => λv: Vector [n + 1] => e) in
         #showtype(first 0 (newVec 1))
       end""".stripMargin)
  do
    val syntax = Parser(tokens).program()
    val reduced = WeakNormalHeadNormalizer.normalize(new SymbolContext(), syntax, Map(
      "showtype" -> ((node: SyntaxNode, context: SymbolContext) => println(s"TypeOf{${pprint(node)}} = ${pprint(typeOf(context, node, Map.empty).get)}"))
    ))
    reduced.map(pprint).foreach(println)