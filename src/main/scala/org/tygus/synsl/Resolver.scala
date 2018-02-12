package org.tygus.synsl


import org.tygus.synsl.language.Expressions.Ident
import org.tygus.synsl.logic._

object Resolver {

  /**
    * Collect program declarations into an environment
    * TODO: type checking
    */
  def resolveProgram(prog: Program): (Seq [GoalFunction], Environment) = {
    val (goals, preds) = prog.decls.foldLeft((Nil : List[GoalFunction], Map.empty[Ident, InductiveDef]))((arg, decl) => {
      val (gs, ps) = arg
      decl match {
        case p@InductiveDef(name, _, _) => (gs, ps + (name -> p))
        case g@GoalFunction(_, _, _) => (g :: gs, ps)
      }
    }
    )
    (goals, Environment(preds))
  }
}
