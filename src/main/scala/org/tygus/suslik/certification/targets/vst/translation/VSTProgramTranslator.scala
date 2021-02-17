package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.targets.vst.Types.{VSTCType, VSTType}
import org.tygus.suslik.certification.targets.vst.logic.Expressions.ProofCExpr
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.VSTPredicate
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep.{Forward, ForwardIf, ValidPointer}
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.certification.traversal.Translator.Result
import org.tygus.suslik.certification.traversal.{Evaluator, Translator}
import org.tygus.suslik.language.Expressions.{Expr, Var}
import org.tygus.suslik.language.SSLType
import org.tygus.suslik.certification.SuslikProofStep
import org.tygus.suslik.certification.targets.vst.clang.Statements.StatementStep
import org.tygus.suslik.certification.targets.vst.translation.VSTProofTranslator.VSTClientContext

import scala.collection.immutable.Queue

object VSTProgramTranslator { case class VSTProgramContext(typing_context: Map[String, VSTCType]) extends ClientContext[VSTProofStep] { } }

class VSTProgramTranslator extends Translator[SuslikProofStep, StatementStep, VSTProgramTranslator.VSTProgramContext] {
  type Deferred = Evaluator.Deferred[StatementStep, VSTProgramTranslator.VSTProgramContext]
  private val no_deferreds: Queue[Deferred] = Queue()

  def with_no_op (implicit context: VSTClientContext) = (List(), List((Queue(), context)))

  override def translate(value: SuslikProofStep, clientContext: VSTProgramTranslator.VSTProgramContext): Result[StatementStep, VSTProgramTranslator.VSTProgramContext] = {
    implicit ctx : VSTProgramTranslator.VSTProgramContext => clientContext
    value match {
      case SuslikProofStep.NilNotLval(vars) => ???
      case SuslikProofStep.CheckPost(prePhi, postPhi) => ???
      case SuslikProofStep.Pick(from, to) => ???
      case SuslikProofStep.Branch(cond, bLabel) => ???
      case SuslikProofStep.Write(stmt) => ???
      case SuslikProofStep.WeakenPre(unused) => ???
      case SuslikProofStep.EmpRule(label) => ???
      case SuslikProofStep.PureSynthesis(is_final, assignments) => ???
      case SuslikProofStep.Open(pred, fresh_vars, sbst, selectors) => ???
      case SuslikProofStep.SubstL(from, to) => ???
      case SuslikProofStep.SubstR(from, to) => ???
      case SuslikProofStep.Read(ghostFrom, ghostTo, operation) => ???
      case SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, gamma) => ???
      case SuslikProofStep.HeapUnify(subst) => ???
      case SuslikProofStep.HeapUnifyPointer(from, to) => ???
      case SuslikProofStep.FrameUnfold(h_pre, h_post) => ???
      case SuslikProofStep.Call(subst, call) => ???
      case SuslikProofStep.Free(stmt, size) => ???
      case SuslikProofStep.Malloc(ghostFrom, ghostTo, stmt) => ???
      case SuslikProofStep.Close(app, selector, asn, fresh_exist) => ???
      case SuslikProofStep.StarPartial(new_pre_phi, new_post_phi) => ???
      case SuslikProofStep.PickCard(from, to) => ???
      case SuslikProofStep.PickArg(from, to) => ???
      case SuslikProofStep.Init(goal) => ???
      case SuslikProofStep.Inconsistency(label) => ???
    }
  }
}