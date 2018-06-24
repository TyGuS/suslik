package org.tygus.synsl.logic

import org.tygus.synsl.language._

object Resolver {

  /**
    * Collect program declarations into an environment
    * TODO: type checking
    */
  def resolveProgram(prog: Program): (Seq [FunSpec], Environment) = {
    val (goals, preds) =
      prog.decls.foldLeft((Nil: List[FunSpec], Map.empty[Ident, InductivePredicate]))((acc, decl) => {
        val (gs, ps) = acc
        decl match {
          case p@InductivePredicate(name, _, _) => (gs, ps + (name -> p))
          case g@FunSpec(_, _, _, _, _) => (g :: gs, ps)
        }
      }
      )
    (goals, Environment(preds, Map.empty))
  }
}
