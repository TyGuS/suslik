package org.tygus.suslik.logic

import org.tygus.suslik.language.Statements.Statement

object Resolver {

  /**
    * Collect program declarations into an environment
    * TODO: type checking
    */
  def resolveProgram(prog: Program): (Seq [FunSpec], Environment, Statement) = {
    val Program(preds, funs, goal) = prog
    val funMap = funs.map(fs => fs.name -> setUpAuxiliaryFunction(fs)).toMap
    val predMap = preds.map(ps => ps.name -> ps).toMap

    val time0 = System.currentTimeMillis()
    (List(goal.spec), Environment(predMap, funMap, startTime = time0), goal.body)
  }

  def setUpAuxiliaryFunction(fs: FunSpec) : FunSpec = {
    // TODO: This is not optimal and, in principle, can lead to infinite derivations
    // However, a generalisation, enabling multiple calls would be too much of a hassle
    // A temporary solution is to kick this function out of the environment, once used
    val newPre = fs.pre.moveToLevel2()
    val newPost = fs.post.lockSAppTags()
    fs.copy(pre = newPre, post = newPost)
  }
}
