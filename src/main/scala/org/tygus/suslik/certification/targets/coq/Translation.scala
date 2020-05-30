package org.tygus.suslik.certification.targets.coq

import org.tygus.suslik.certification.targets.coq.language.Expressions._
import org.tygus.suslik.certification.targets.coq.language._
import org.tygus.suslik.certification.targets.coq.logic._
import org.tygus.suslik.language._
import org.tygus.suslik.logic._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.logic.unification.SpatialUnification
import org.tygus.suslik.synthesis.SearchTree
import org.tygus.suslik.synthesis.SearchTree._
import org.tygus.suslik.synthesis.rules._
import org.tygus.suslik.synthesis.rules.OperationalRules._
import org.tygus.suslik.synthesis.rules.LogicalRules._
import org.tygus.suslik.synthesis.rules.Rules._
import org.tygus.suslik.synthesis.rules.UnfoldingRules._

object Translation {
  case class TranslationException(msg: String) extends Exception(msg)

  lazy val rootOr: OrNode = SearchTree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))
  lazy val rootAnd: AndNode = rootOr.child.getOrElse(throw TranslationException("Search tree is uninitialized"))

  // Basic check whether a proof is inductive
  lazy val inductive: Boolean = rootAnd.rule == Open

  def translateProof(proc: Procedure)(implicit env: Environment): CProof = {
    def expandStmt(stmt: Statement) : (Option[Statement], Seq[Statement]) = stmt match {
      case SeqComp(s1, s2) => (Some(s1), Seq(s2))
      case If(_, tb, eb) => (None, Seq(tb, eb))
      case Guarded(_, body, els, _) => (None, Seq(body, els))
      case _ => (Some(stmt), Seq())
    }

    @scala.annotation.tailrec
    def unwrapStmtProducer(p: StmtProducer) : StmtProducer = p match {
      case PartiallyAppliedProducer(p, _) => unwrapStmtProducer(p)
      case ChainedProducer(p1, _) => unwrapStmtProducer(p1)
      case p => p
    }

    /**
      * Creates a new continuation B that applies the existing continuation A
      * to a new sequence prepended to A's original parameter sequence
      */
    def prependKont(kont: Seq[CProofStep] => CProofStep, prependSteps: Seq[CProofStep])(steps: Seq[CProofStep]) =
      kont(prependSteps ++ steps)

    // Double tree walk: program and proof
    def traverse(an: SearchTree.AndNode, stmt: Statement, cenv: CEnvironment, kont: Seq[CProofStep] => CProofStep): CProofStep = {
      val (currStmt, nextStmts) = expandStmt(stmt)

      val on = an.parent
      val goal = on.goal
      val footprint = an.consume
      val subOns = an.children.reverse.map(_.child).filter(_.isDefined).map(_.get)
      val stmtProducer = unwrapStmtProducer(an.kont)
      val ruleApp: Option[CRuleApp] = (an.rule, stmtProducer) match {
        case (EmpRule, _) =>
          Some(CEmp)
        case (ReadRule, PrependProducer(Load(to, _, _, _))) =>
          currStmt match {
            case Some(Load(to1, _, _, _)) if to.name.startsWith(to1.name) =>
              Some(CRead)
            case _ =>
              None // bound variable was eliminated by SeqComp.simplify
          }
        case (WriteRule, PrependProducer(Store(to, _, _))) =>
          Some(CWrite(CVar(to.name)))
        case (FreeRule, PrependProducer(Free(v))) =>
          footprint.pre.blocks.find(_.loc == v)
            .map(b => CFreeRuleApp(b.sz))
        case (CallRule, PrependProducer(Call(fun, args, _))) =>
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
          val csub = sub.map { case (k, v) => (CVar(k.name), translateExpr(v))}
          Some(CCallRuleApp(cenv, fun.name, args.map(arg => translateExpr(arg).asInstanceOf[CVar]), csub))
        case (Open, BranchProducer(selectors)) =>
          val app = footprint.pre.apps.headOption.getOrElse(throw TranslationException("Open rule was called, but no predicate applications found"))
          Some(COpen(cenv, selectors.map(translateExpr), translateHeaplet(app).asInstanceOf[CSApp]))
        case _ =>
          None // rule has no effect on certification
      }

      ruleApp match {
        case Some(app) =>
          val nextEnv = app.nextEnvs(cenv, translateGoal(goal))
          subOns.zip(nextStmts).zip(nextEnv) match {
            case ((subOn, nextStmt), nextEnv) :: tl =>
              val nextKont = tl.foldLeft((steps: Seq[CProofStep]) => kont(Seq(CProofStep(app, steps)))) {
                case (kontAcc, ((subOn, nextStmt), nextEnv)) =>
                  (steps: Seq[CProofStep]) =>
                    traverse(subOn, nextStmt, nextEnv, prependKont(kontAcc, steps))
              }
              traverse(subOn, nextStmt, nextEnv, nextKont)
            case Nil =>
              kont(Seq(CProofStep(app, Seq()))) // nothing left to traverse
          }
        case None =>
          // No Coq proof step was generated for this run; pass through the parameters
          subOns match {
            case subOn :: tl =>
              val nextKont = tl.foldLeft(kont) {
                case (kontAcc, subOn) =>
                  (steps: Seq[CProofStep]) =>
                    traverse(subOn, stmt, cenv, prependKont(kontAcc, steps))
              }
              traverse(subOn, stmt, cenv, nextKont)
            case Nil =>
              kont(Seq()) // nothing left to traverse
          }

          traverse(subOns.head, stmt, cenv, kont)
      }
    }

    val initialGoal = translateGoal(rootOr.goal)
    val cenv = CEnvironment(
      initialGoal,
      translateFunSpec,
      Map.empty,
      env.predicates.mapValues(translateInductivePredicate),
      Seq.empty,
      inductive
    )
    val ruleApp = CGhostElim(cenv)
    val nextEnv = ruleApp.nextEnvs(cenv, initialGoal)
    val res = traverse(rootAnd, proc.body, nextEnv.head, steps => CProofStep(ruleApp, steps))

    CProof(res)
  }

  def translateFunSpec(implicit env: Environment): CFunSpec = {
    val FunSpec(_, tp, _, _, _, _) = rootOr.goal.toFunSpec
    val goal = rootOr.goal
    val pureParams = goal.universalGhosts
      .intersect(goal.gamma.keySet)
      .map(v => translateParam((goal.gamma(v), v))).toList
    val ctp = translateSSLType(tp)
    val cparams = goal.formals.map(translateParam)
    val cpre = translateAsn(goal.pre)
    val cpost = translateAsn(goal.post)
    CFunSpec(
      goal.fname,
      ctp,
      cparams,
      pureParams,
      cpre,
      cpost,
      inductive
    )
  }

  def translateInductivePredicate(el: InductivePredicate): CInductivePredicate = {
    val cParams = el.params.map(translateParam) :+ (CHeapType, CVar("h"))
    val cClauses = el.clauses.zipWithIndex.map { case (c, i) => translateClause(s"${el.name}$i", c) }
    CInductivePredicate(el.name, cParams, cClauses)
  }

  private def translateParam(el: (SSLType, Var)): (CoqType, CVar) =
    (translateSSLType(el._1), CVar(el._2.name))

  private def translateClause(name: String, el: InductiveClause): CInductiveClause = {
    val selector = translateExpr(el.selector)
    CInductiveClause(name, selector, translateAsn(el.asn))
  }


  def translateSSLType(el: SSLType): CoqType = el match {
    case BoolType => CBoolType
    case IntType => CNatType
    case LocType => CPtrType
    case IntSetType => CNatSeqType
    case VoidType => CUnitType
  }

  def translateGoal(goal: Goal): CGoal = {
    val pre = translateAsn(goal.pre)
    val post = translateAsn(goal.post)
    val gamma = goal.gamma.map { case (value, lType) => (CVar(value.name), translateSSLType(lType)) }
    val programVars = goal.programVars.map(v => CVar(v.name))
    val universalGhosts = goal.universalGhosts.intersect(goal.gamma.keySet).map(v => CVar(v.name)).toSeq
    CGoal(pre, post, gamma, programVars, universalGhosts, goal.fname)
  }

  private def translateExpr(el: Expr): CExpr = el match {
    case Var(name) => CVar(name)
    case BoolConst(value) => CBoolConst(value)
    case IntConst(value) => CNatConst(value)
    case el@UnaryExpr(_, _) => translateUnaryExpr(el)
    case el@BinaryExpr(_, _, _) => translateBinaryExpr(el)
    case el@OverloadedBinaryExpr(_, _, _) => translateOverloadedBinaryExpr(el)
    case SetLiteral(elems) => CSetLiteral(elems.map(e => translateExpr(e)))
    case IfThenElse(c, t, e) => CIfThenElse(translateExpr(c), translateExpr(t), translateExpr(e))
  }

  private def translateHeaplet(el: Heaplet): CExpr = el match {
    case PointsTo(loc, offset, value) => CPointsTo(translateExpr(loc), offset, translateExpr(value))
    case SApp(pred, args, tag, card) => CSApp(pred, args.map(translateExpr), tag)
  }

  private def translateAsn(el: Assertion): CAssertion =
    CAssertion(translateExpr(el.phi.toExpr), translateSFormula(el.sigma))

  private def translateSFormula(el: SFormula): CSFormula = {
    val ptss = el.ptss.map(translateHeaplet).asInstanceOf[List[CPointsTo]]
    val apps = el.apps.map(translateHeaplet).asInstanceOf[List[CSApp]]
    CSFormula("h", apps, ptss)
  }

  private def translateUnaryExpr(el: UnaryExpr) : CExpr = el match {
    case UnaryExpr(OpNot, e) => e match {
      case BinaryExpr(OpEq, left, right) => COverloadedBinaryExpr(COpNotEqual, translateExpr(left), translateExpr(right))
      case _ => CUnaryExpr(COpNot, translateExpr(e))
    }
    case UnaryExpr(OpUnaryMinus, e) => ???
  }

  private def translateOverloadedBinaryExpr(el: OverloadedBinaryExpr) : CExpr = el match {
    case OverloadedBinaryExpr(OpOverloadedEq, l, r) =>
      COverloadedBinaryExpr(COpOverloadedEq, translateExpr(l), translateExpr(r))
    case OverloadedBinaryExpr(OpNotEqual, l, r) =>
      COverloadedBinaryExpr(COpNotEqual, translateExpr(l), translateExpr(r))
    case OverloadedBinaryExpr(OpGt, l, r) =>
      COverloadedBinaryExpr(COpGt, translateExpr(l), translateExpr(r))
    case OverloadedBinaryExpr(OpGeq, l, r) =>
      COverloadedBinaryExpr(COpGeq, translateExpr(l), translateExpr(r))
    case OverloadedBinaryExpr(OpGeq, l, r) =>
      COverloadedBinaryExpr(COpGeq, translateExpr(l), translateExpr(r))
    case OverloadedBinaryExpr(OpOverloadedPlus, l, r) =>
      COverloadedBinaryExpr(COpOverloadedPlus, translateExpr(l), translateExpr(r))
    case OverloadedBinaryExpr(OpOverloadedMinus, l, r) =>
      COverloadedBinaryExpr(COpOverloadedMinus, translateExpr(l), translateExpr(r))
    case OverloadedBinaryExpr(OpOverloadedLeq, l, r) =>
      COverloadedBinaryExpr(COpOverloadedLeq, translateExpr(l), translateExpr(r))
    case OverloadedBinaryExpr(OpOverloadedStar, l, r) =>
      COverloadedBinaryExpr(COpOverloadedStar, translateExpr(l), translateExpr(r))
  }

  private def translateBinaryExpr(el: BinaryExpr) : CExpr = el match {
    case BinaryExpr(OpImplication, l, r) =>
      CBinaryExpr(COpImplication, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpPlus, l, r) =>
      CBinaryExpr(COpPlus, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpMinus, l, r) =>
      CBinaryExpr(COpMinus, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpMultiply, l, r) =>
      CBinaryExpr(COpMultiply, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpEq, l, r) =>
      CBinaryExpr(COpEq, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpBoolEq, l, r) =>
      CBinaryExpr(COpBoolEq, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpLeq, l, r) =>
      CBinaryExpr(COpLeq, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpLt, l, r) =>
      CBinaryExpr(COpLt, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpAnd, l, r) =>
      CBinaryExpr(COpAnd, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpOr, l, r) =>
      CBinaryExpr(COpOr, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpUnion, l, r) =>
      CBinaryExpr(COpUnion, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpDiff, l, r) =>
      CBinaryExpr(COpDiff, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpIn, l, r) =>
      CBinaryExpr(COpIn, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpSetEq, l, r) =>
      CBinaryExpr(COpSetEq, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpSubset, l, r) =>
      CBinaryExpr(COpSubset, translateExpr(l), translateExpr(r))
    case BinaryExpr(OpIntersect, l, r) =>
      CBinaryExpr(COpIntersect, translateExpr(l), translateExpr(r))
  }
}
