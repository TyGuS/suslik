package org.tygus.suslik.certification.targets.coq.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.certification.targets.coq.logic.Proof._
import org.tygus.suslik.certification.targets.coq.logic.rules.FailRules.CAbduceBranchApp
import org.tygus.suslik.certification.targets.coq.logic.rules.LogicalRules._
import org.tygus.suslik.certification.targets.coq.logic.rules.NativeRules.CGhostElimApp
import org.tygus.suslik.certification.targets.coq.logic.rules.OperationalRules._
import org.tygus.suslik.certification.targets.coq.logic.rules.Rules.CRuleApp
import org.tygus.suslik.certification.targets.coq.logic.rules.UnfoldingRules._
import org.tygus.suslik.certification.targets.coq.logic.rules.UnificationRules.CPickApp
import org.tygus.suslik.certification.targets.coq.translation.Translation._
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.SepLogicUtils
import org.tygus.suslik.logic.unification.SpatialUnification
import org.tygus.suslik.synthesis.rules.BranchRules.AbduceBranch
import org.tygus.suslik.synthesis.rules.LogicalRules.EmpRule
import org.tygus.suslik.synthesis.rules.OperationalRules._
import org.tygus.suslik.synthesis.rules.UnfoldingRules
import org.tygus.suslik.synthesis.rules.UnfoldingRules._
import org.tygus.suslik.synthesis.{BranchProducer, ExistentialProducer, GuardedProducer, PrependProducer}

object ProofTranslation extends SepLogicUtils {
  type ProofProducer = Producer[CProofStep]

  private case class TraversalItem(node: CertTree.Node, stmt: Statement, cenv: CEnvironment) extends Traversable

  def translate(node: CertTree.Node, proc: Procedure, goal: CGoal, cenv: CEnvironment): CProof = {
    val ruleApp = CGhostElimApp(goal, cenv)
    val nextEnv = ruleApp.nextEnvs.head

    val traversalItem = TraversalItem(node, proc.body, nextEnv)
    val proofBody = traverseProof(traversalItem, ruleAppProducer(ruleApp))
    CProof(proofBody)
  }

  private def joinProofProducer(steps: List[TraversalItem], kont: ProofProducer): ProofProducer =
    joinProducer[CProofStep, TraversalItem](traverseProof)(steps, kont)

  private def ruleAppProducer(app: CRuleApp): ProofProducer = steps => CProofStep(app, steps)

  private def deriveCRuleApp(item: TraversalItem, currStmt: Option[Statement]): Option[CRuleApp] = {
    val TraversalItem(node, _, cenv) = item

    val goal = node.goal
    // TODO: check this
    val parentPre = node.goal.parent.map(_.pre.sigma).getOrElse(emp)
    val stmtProducer = unwrapStmtProducer(node.kont)
    (node.rule, stmtProducer) match {
      case (EmpRule, _) =>
        Some(CEmpApp(cenv))
      case (ReadRule, PrependProducer(Load(to, _, _, _))) =>
        currStmt match {
          case Some(Load(to1, _, _, _)) if to.name.startsWith(to1.name) =>
            Some(CReadApp(cenv))
          case _ =>
            None // bound variable was eliminated by SeqComp.simplify
        }
      case (WriteRule, PrependProducer(Store(to, _, _))) =>
        Some(CWriteApp(CVar(to.name), cenv))
      case (FreeRule, PrependProducer(Free(v))) =>
        parentPre.blocks.find(_.loc == v).map(b => CFreeApp(b.sz, cenv))
      case (CallRule, PrependProducer(Call(fun, _, _))) =>
        val allCands = goal.companionCandidates.reverse
        val cands = if (goal.env.config.auxAbduction) allCands else allCands.take(1)
        val funLabels = cands.map(a => a.toFunSpec) ++ // companions
          goal.env.functions.values // components

        val subs = for {
          f <- funLabels

          // Find all subsets of the goal's pre that might be unified
          lilHeap = f.pre.sigma
          largHeap = goal.pre.sigma
          largSubHeap <- UnfoldingRules.findLargestMatchingHeap(lilHeap, largHeap)
          callSubPre = goal.pre.copy(sigma = largSubHeap)

          // Try to unify f's precondition and found goal pre's subheaps
          sourceAsn = f.pre
          targetAsn = callSubPre
          sub <- SpatialUnification.unify(targetAsn, sourceAsn)
        } yield sub

        val sub = subs.head
        val existingVars = cenv.ctx
        def longestPrefix(s: String, vset: Set[CVar]): Option[CVar] = {
          val prefixes = vset.filter(v1 => s.startsWith(v1.name))
          if (prefixes.isEmpty) None
          else Some(prefixes.maxBy(_.name.length))
        }

        val csub = sub.map { case (src, dest) =>
          val csrc = CVar(src.name)
          // if any variables were renamed, substitute them
          val simplifyingMapping = dest.vars
            .map(v => (v, longestPrefix(v.name, existingVars)))
            .filter(_._2.isDefined)
            .map(el => (el._1, Var(el._2.get.name)))
            .toMap
          (csrc, translateExpr(dest.subst(simplifyingMapping)))
        }
        Some(CCallApp(fun.name, csub, cenv))
      case (Open, BranchProducer(selectors)) =>
        val app = parentPre.apps.headOption
          .getOrElse(throw TranslationException("Open rule was called, but no predicate applications found"))
        val pred = cenv.predicates
          .find(_.name == app.pred)
          .getOrElse(throw TranslationException(s"No predicate matching label ${app.pred} found in environment"))
        Some(COpenApp(selectors.map(translateExpr), pred, cenv))
      case (_, ExistentialProducer(subst)) =>
        val csubst = subst.map { case (k, v) => CVar(k.name) -> translateExpr(v) }
        Some(CPickApp(csubst, cenv))
      case (AbduceBranch, GuardedProducer(cond)) =>
        Some(CAbduceBranchApp(translateExpr(cond), cenv))
      case _ =>
        None // rule has no effect on certification
    }
  }

  @scala.annotation.tailrec
  private def traverseProof(item: TraversalItem, kont: ProofProducer): CProofStep = {
    val (currStmt, nextStmts) = expandStmt(item.stmt)
    val childNodes = item.node.children
    val (nextTraversalItems, nextKont) = deriveCRuleApp(item, currStmt) match {
      case Some(cruleApp) =>
        val nextTraversalItems = childNodes
          .zip(if (cruleApp.isExplicit) nextStmts else Seq(item.stmt))
          .zip(cruleApp.nextEnvs)
          .map(i => TraversalItem(i._1._1, i._1._2, i._2))
        val nextKont = composeProducer[CProofStep](ruleAppProducer(cruleApp), kont)
        (nextTraversalItems, nextKont)
      case _ =>
        (childNodes.map(TraversalItem(_, item.stmt, item.cenv)), kont)
    }

    nextTraversalItems match {
      case hd :: tl =>
        traverseProof(hd, joinProofProducer(tl, nextKont))
      case Nil =>
        nextKont(List.empty)
    }
  }
}
