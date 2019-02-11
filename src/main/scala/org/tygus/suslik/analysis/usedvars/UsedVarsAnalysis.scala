package org.tygus.suslik.analysis.usedvars

import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.Statements.{Call, Error, Free, Guarded, If, Load, Magic, Malloc, Procedure, SeqComp, Skip, Statement, Store}
import org.tygus.suslik.util.StringUtil.mkSpaces

object UsedVarsAnalysis {

  type ProcName = String
  type UsageMap = Map[(Var, ProcName), Usage]
  type ProcedureMap = Map[ProcName, Procedure]
  type ConvergedProcs = Set[ProcName]
  type Context = String

  def analyseTopLevel(main: Procedure, pmap: ProcedureMap): UsageMap = {
    val initMap: UsageMap =
      main.formals.map { case (_, v) => ((v, main.name), NotUsed) }.toMap
    val initCall = Call(None, Var(main.name), main.formals.map(_._2), None)
    analysisLoop(List((initCall.fun.name, initCall)), initMap, Set.empty, pmap)
  }

  def analysisLoop(calls: List[(Context, Call)], usages: UsageMap,
                   converged: ConvergedProcs, pmap: ProcedureMap): UsageMap = {
    calls match {
      case Nil => usages
      // No need to analyse already
      case (ctx, c) :: moreCalls if !converged.contains(c.fun.name) =>
        analysisLoop(moreCalls, usages, converged, pmap)
      // Let's analyse this function
      case (ctx, c) :: moreCalls =>
        // Analyse a new call
        pmap.get(c.fun.name) match {
          case Some(Procedure(name, _, formals, body)) =>

            // Adding parameters of the call to be analysed
            val addedParams = usages ++ formals.map {
              case (_, p) =>
                val u = usages.getOrElse((p, name), NotUsed)
                ((p, name), NotUsed.join(u))
            }
            val (newUsages, newCalls) = findUsedInStmt(body, usages, ctx, pmap)

            // Determine if there is an effect of analysing this thing
            val noNewDiscoveries = newUsages.forall { case ((v, p), u) =>
              val oldUsage = addedParams.getOrElse((v, p), NotUsed)
              oldUsage == u
            }
            val newConverged: ConvergedProcs =
              if (!noNewDiscoveries) converged + name
              else converged

            // Removing converged calls
            val nextCalls = (moreCalls ++ newCalls.map(x => (ctx, x))).filter {
              case (_, Call(_, Var(z), _, _)) => !newConverged.contains(z)
            }

            // TODO: Add information about parameters of this context [ctx] (i.e., caller) out of this call [c] (caller)


            analysisLoop(nextCalls, newUsages, newConverged, pmap)
          case None =>
            println(s"No function with name ${c.fun.name} found!")
            analysisLoop(moreCalls, usages, converged, pmap)
        }
    }
  }

  def findUsedInStmt(stmt: Statement,
                     umap: UsageMap,
                     ctx: Context,
                     pmap: ProcedureMap): (UsageMap, List[Call]) = stmt match {
    case Skip => ???
    case Error => ???
    case Magic => ???
    case Malloc(to, _, sz) => ???
    case Free(v) => ???
    case Store(to, off, e) => ???
    case Load(to, _, from, off) => ???
    case Call(tt, fun, args, _) => ???
    case SeqComp(s1, s2) => ???
    case If(cond, tb, eb) => ???
    case Guarded(cond, b) => ???
  }

}


abstract class Usage {
  def join(other: Usage): Usage
}

// Bottom
case object NotUsed extends Usage {
  override def join(other: Usage): Usage = other
}

// Top
case object ProbablyUsed extends Usage {
  override def join(other: Usage): Usage = ProbablyUsed
}
