package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.{CertTree, ProofRule}
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.program.Statements._
import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.logic.Proof
import org.tygus.suslik.certification.targets.htt.logic.Sentences._
import org.tygus.suslik.certification.targets.htt.translation.IR.translateGoal
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic._

object Translation {
  case class TranslationException(msg: String) extends Exception(msg)

  /**
    * Produces the components of a HTT certificate, from the tree of successful derivations and a synthesized procedure
    * @param node the root of the derivation tree
    * @param proc the synthesized procedure
    * @param env the synthesis environment
    * @return the inductive predicates, fun spec, proof, and program translated to HTT
    */
  def translate(node: CertTree.Node, proc: Procedure)(implicit env: Environment):
    (Map[String, CInductivePredicate], CFunSpec, Proof.Step, CProcedure) = {
    val cpreds = env.predicates.mapValues(p => {
      val gamma = p.resolve(p.params.toMap, env).get
      val p1 = p.copy(clauses = p.clauses.map(_.resolveOverloading(gamma)))
      translateInductivePredicate(p1, gamma)
    })
    val goal = translateGoal(node.goal)
    val ctx = IR.emptyContext.copy(predicateEnv = cpreds)
    val ir = IR.fromRule(ProofRule.Init(node.goal, ProofRule.of_certtree(node)), ctx).propagateContext
    val proof = ProofTranslation.translate(ir)
    val progBody = ProgramTranslation.translate(ir)
    val cproc = CProcedure(proc.name, translateType(proc.tp), proc.formals.map(translateParam), progBody)
    (cpreds, goal.toFunspec, proof, cproc)
  }

  private def translateInductivePredicate(el: InductivePredicate, gamma: Gamma): CInductivePredicate = {
    val cParams = el.params.map(translateParam) :+ (CHeapType, CVar("h"))
    val cGamma = gamma.map { case (v, t) => (CVar(v.name), translateType(t))}

    val cClauses = el.clauses.zipWithIndex.map { case (c, idx) =>
      val selector = translateExpr(c.selector)
      val asn = translateAsn(c.asn)

      // Include the clause number so that we can use Coq's `constructor n` tactic
      CInductiveClause(el.name, idx + 1, selector, asn, asn.existentials(cParams.map(_._2)))
    }
    CInductivePredicate(el.name, cParams, cClauses, cGamma)
  }

  def translateParam(el: (Var, SSLType)): (HTTType, CVar) =
    (translateType(el._2), translateVar(el._1))

  def translateType(el: SSLType): HTTType = el match {
    case BoolType => CBoolType
    case IntType => CNatType
    case LocType => CPtrType
    case IntSetType => CNatSeqType
    case VoidType => CUnitType
    case CardType => CCardType
  }

  def translateExpr(el: Expr): CExpr = el match {
    case Var(name) => CVar(name)
    case BoolConst(value) => CBoolConst(value)
    case LocConst(value) => CPtrConst(value)
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
    val conjuncts = el.phi.conjuncts.toSeq.map(c => translateExpr(c).simplify).filterNot(_.isCard)
    val f = (a1: CExpr, a2: CExpr) => CBinaryExpr(COpAnd, a1, a2)
    val phi = if (conjuncts.isEmpty) CBoolConst(true) else conjuncts.reduce(f)
    val sigma = translateSFormula(el.sigma)
    CAssertion(phi, sigma).removeCardConstraints
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
