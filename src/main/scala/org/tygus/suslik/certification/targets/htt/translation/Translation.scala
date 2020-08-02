package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.Statements._
import org.tygus.suslik.certification.targets.htt.language._
import org.tygus.suslik.certification.targets.htt.logic.Proof.{CEnvironment, CGoal}
import org.tygus.suslik.certification.targets.htt.logic.ProofSteps.Proof
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.logic._

object Translation {
  case class TranslationException(msg: String) extends Exception(msg)

  trait Traversable

  /**
    * Produces a HTT certificate from the tree of successful derivations and a synthesized procedure
    * @param node the root of the derivation tree
    * @param proc the synthesized procedure
    * @param env the synthesis environment
    * @return the inductive predicates, fun spec, proof, and program translated to HTT
    */
  def translate(node: CertTree.Node, proc: Procedure)(implicit env: Environment):
    (Map[String, CInductivePredicate], CFunSpec, Proof, CProcedure) = {
    val cpreds = env.predicates.mapValues(p => translateInductivePredicate(p.resolveOverloading(env)))
    val goal = translateGoal(node.goal)
    val initialCEnv = CEnvironment(goal, cpreds)
    val proof = ProofTranslation.translate(node, initialCEnv)
    val stmtBody = ProgramTranslation.translate(node, proc)

    val cproc = CProcedure(proc.name, translateType(proc.tp), proc.formals.map(translateParam), stmtBody)
    (cpreds, goal.toFunspec, proof, cproc)
  }

  private def translateInductivePredicate(el: InductivePredicate): CInductivePredicate = {
    val cParams = el.params.map(translateParam) :+ (CHeapType, CVar("h"))
    val cClauses = el.clauses.zipWithIndex.map { case (c, i) => translateClause(c, el.name, i, cParams) }
    CInductivePredicate(el.name, cParams, cClauses)
  }

  private def translateParam(el: (Var, SSLType)): (HTTType, CVar) =
    (translateType(el._2), translateVar(el._1))

  private def translateClause(el: InductiveClause, pred: String, idx: Int, predParams: CFormals): CInductiveClause = {
    val selector = translateExpr(el.selector)
    val asn = translateAsn(el.asn)
    CInductiveClause(pred, idx, selector, translateAsn(el.asn), asn.existentials(predParams.map(_._2)))
  }

  def translateType(el: SSLType): HTTType = el match {
    case BoolType => CBoolType
    case IntType => CNatType
    case LocType => CPtrType
    case IntSetType => CNatSeqType
    case VoidType => CUnitType
    case CardType => CCardType
  }

  def translateGoal(goal: Goal): CGoal = {
    val pre = translateAsn(goal.pre)
    val post = translateAsn(goal.post)
    val gamma = goal.gamma.map { case (value, lType) => (translateVar(value), translateType(lType)) }
    val programVars = goal.programVars.map(translateVar)
    val universalGhosts = goal.universalGhosts.map(translateVar).toSeq.filterNot(_.isCard)
    CGoal(pre, post, gamma, programVars, universalGhosts, goal.fname)
  }

  def translateExpr(el: Expr): CExpr = el match {
    case Var(name) => CVar(name)
    case BoolConst(value) => CBoolConst(value)
    case IntConst(value) => CNatConst(value)
    case el@UnaryExpr(_, _) => translateUnaryExpr(el)
    case el@BinaryExpr(_, _, _) => translateBinaryExpr(el)
    case SetLiteral(elems) => CSetLiteral(elems.map(e => translateExpr(e)))
    case IfThenElse(c, t, e) => CIfThenElse(translateExpr(c), translateExpr(t), translateExpr(e))
    case _ => throw TranslationException("Operation not supported")
  }

  def translateVar(el: Var): CVar = CVar(el.name)

  def translateSApp(el: SApp): CSApp = CSApp(el.pred, el.args.map(translateExpr), translateExpr(el.card))
  def translatePointsTo(el: PointsTo): CPointsTo = CPointsTo(translateExpr(el.loc), el.offset, translateExpr(el.value))

  def translateAsn(el: Assertion): CAssertion = {
    val phi: CExpr = translateExpr(el.phi.toExpr).simplify
    val sigma = translateSFormula(el.sigma)
    CAssertion(phi, sigma)
  }

  def translateSFormula(el: SFormula): CSFormula = {
    val ptss = el.ptss.map(translatePointsTo)
    val apps = el.apps.map(translateSApp)
    CSFormula("h", apps, ptss)
  }

  private def translateUnOp(op: UnOp): CUnOp = op match {
    case OpNot => COpNot
    case OpUnaryMinus => COpUnaryMinus
  }

  private def translateBinOp(op: BinOp): CBinOp = op match {
    case OpImplication => COpImplication
    case OpPlus => COpPlus
    case OpMinus => COpMinus
    case OpMultiply => COpMultiply
    case OpEq => COpEq
    case OpBoolEq => COpBoolEq
    case OpLeq => COpLeq
    case OpLt => COpLt
    case OpAnd => COpAnd
    case OpOr => COpOr
    case OpUnion => COpUnion
    case OpDiff => COpDiff
    case OpIn => COpIn
    case OpSetEq => COpSetEq
    case OpSubset => COpSubset
    case OpIntersect => COpIntersect
  }

  private def translateUnaryExpr(el: UnaryExpr) : CExpr =
    CUnaryExpr(translateUnOp(el.op), translateExpr(el.arg))

  private def translateBinaryExpr(el: BinaryExpr) : CExpr =
    CBinaryExpr(translateBinOp(el.op), translateExpr(el.left), translateExpr(el.right))
}
