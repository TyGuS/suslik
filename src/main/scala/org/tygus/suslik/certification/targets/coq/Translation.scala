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
import org.tygus.suslik.certification.Tree
import org.tygus.suslik.synthesis.rules._
import org.tygus.suslik.synthesis.rules.OperationalRules._
import org.tygus.suslik.synthesis.rules.LogicalRules._
import org.tygus.suslik.synthesis.rules.Rules._
import org.tygus.suslik.synthesis.rules.UnfoldingRules._

object Translation {
  case class TranslationException(msg: String) extends Exception(msg)

  lazy val root: Tree.Node = Tree.root.getOrElse(throw TranslationException("Search tree is uninitialized"))
  // Basic check whether a proof is inductive
  lazy val inductive: Boolean = root.rule == Open

  type ProofProducer = Seq[CProofStep] => CProofStep

  def translateProof(proc: Procedure)(implicit env: Environment): CProof = {
    case class TraversalItem(node: Tree.Node, stmt: Statement, cenv: CEnvironment)

    /**
      * Given a program point, derives the currently focused statement and its children
      * @param stmt the program point
      * @return a tuple of an optional current statement and a sequence of child statements
      */
    def expandStmt(stmt: Statement) : (Option[Statement], Seq[Statement]) = stmt match {
      case SeqComp(s1, s2) => (Some(s1), Seq(s2))
      case If(_, tb, eb) => (None, Seq(tb, eb))
      case Guarded(_, body, els, _) => (None, Seq(body, els))
      case _ => (Some(stmt), Seq())
    }

    /**
      * Unwraps a statement producer to get to the part relevant to certification
      * @param p the producer
      * @return an unwrapped producer
      */
    @scala.annotation.tailrec
    def unwrapStmtProducer(p: StmtProducer) : StmtProducer = p match {
      case PartiallyAppliedProducer(p, _) => unwrapStmtProducer(p)
      case ChainedProducer(p1, _) => unwrapStmtProducer(p1)
      case p => p
    }

    /**
      * Composes two continuation functions g ∘ f
      * @param f the first continuation to apply
      * @param g the second continuation to apply
      * @return the composed result
      */
    def composeProducer(f: ProofProducer, g: ProofProducer): ProofProducer = items => g(Seq(f(items)))

    /**
      * Creates a new continuation that prepends items to the argument of an existing continuation `kont`
      * @param kont the original continuation
      * @param itemsToPrepend items to prepend to `kont`
      * @return a new continuation
      */
    def prependArgsProducer(kont: ProofProducer, itemsToPrepend: Seq[CProofStep]): ProofProducer =
      items => kont(itemsToPrepend ++ items)

    /**
      * Creates a new continuation that combines the result of multiple traversals at a branching point
      * @param items a list of things to traverse
      * @param kont the final (root) continuation to apply after collecting all child results
      * @return a new continuation
      */
    def branchProducer(items: List[TraversalItem], kont: ProofProducer): ProofProducer =
      items.foldLeft(kont) {
        case (kontAcc, item) =>
          items1 => traverse(item, prependArgsProducer(kontAcc, items1))
      }

    /**
      * Tries to derive a Coq rule application that matches a given traversal item
      * @param item the thing to traverse
      * @return an optional Coq rule application
      */
    def deriveCRuleApp(item: TraversalItem): Option[CRuleApp] = {
      implicit val TraversalItem(node, stmt, cenv) = item
      val (currStmt, _) = expandStmt(stmt)

      val goal = node.goal
      val footprint = node.consume
      val stmtProducer = unwrapStmtProducer(node.kont)
      (node.rule, stmtProducer) match {
        case (EmpRule, _) =>
          Some(CEmp())
        case (ReadRule, PrependProducer(Load(to, _, _, _))) =>
          currStmt match {
            case Some(Load(to1, _, _, _)) if to.name.startsWith(to1.name) =>
              Some(CRead())
            case _ =>
              None // bound variable was eliminated by SeqComp.simplify
          }
        case (WriteRule, PrependProducer(Store(to, _, _))) =>
          Some(CWrite(CVar(to.name)))
        case (FreeRule, PrependProducer(Free(v))) =>
          footprint.pre.blocks.find(_.loc == v)
            .map(b => CFreeRuleApp(b.sz))
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
          val csub = sub.map { case (src, dest) =>
            val csrc = CVar(src.name)
            // if any variables were renamed, substitute them
            val existingVars = cenv.ctx.keySet
            val simplifyingMapping = dest.vars
              .map(v => (v, existingVars.find(v1 => v.name.startsWith(v1.name))))
              .filter(_._2.isDefined)
              .map(el => (el._1, Var(el._2.get.name)))
              .toMap
            (csrc, translateExpr(dest.subst(simplifyingMapping)))
          }
          Some(CCallRuleApp(fun.name, csub))
        case (Open, BranchProducer(selectors)) =>
          val app = footprint.pre.apps.headOption
            .getOrElse(throw TranslationException("Open rule was called, but no predicate applications found"))
          Some(COpen(selectors.map(translateExpr), translateInductivePredicate(env.predicates(app.pred))))
        case _ =>
          None // rule has no effect on certification
      }
    }

    /**
      * CPS tree traversal of a proof and program in tandem
      * @param item the current thing to traverse
      * @param kont the current continuation
      * @return a Coq proof step
      */
    @scala.annotation.tailrec
    def traverse(item: TraversalItem, kont: ProofProducer): CProofStep = {
      val ruleApp = deriveCRuleApp(item)

      val (_, nextStmts) = expandStmt(item.stmt)
      val childNodes = item.node.children
      val (nextTraversalItems, nextKont) = ruleApp match {
        case Some(app) =>
          val nextEnvs = app.nextEnvs(translateGoal(item.node.goal))
          val nextTraversalItems = childNodes.zip(nextStmts).zip(nextEnvs).map(i => TraversalItem(i._1._1, i._1._2, i._2))
          val nextKont = composeProducer(steps => CProofStep(app, steps), kont)
          (nextTraversalItems, nextKont)
        case None =>
          (childNodes.map(TraversalItem(_, item.stmt, item.cenv)), kont)
      }

      nextTraversalItems match {
        case hd :: tl =>
          traverse(hd, branchProducer(tl, nextKont))
        case Nil =>
          nextKont(Seq())
      }
    }

    val initialGoal = translateGoal(root.goal)
    val initialCEnv: CEnvironment = CEnvironment(translateFunSpec, Map.empty, Seq.empty)
    val ruleApp = CGhostElim(initialGoal)(initialCEnv)
    val nextEnv = ruleApp.nextEnvs(initialGoal).head
    val res = traverse(TraversalItem(root, proc.body, nextEnv), steps => CProofStep(ruleApp, steps))

    CProof(res)
  }

  def translateFunSpec(implicit env: Environment): CFunSpec = {
    val FunSpec(_, tp, _, _, _, _) = root.goal.toFunSpec
    val goal = root.goal
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
