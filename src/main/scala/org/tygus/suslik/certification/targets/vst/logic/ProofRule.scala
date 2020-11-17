package org.tygus.suslik.certification.targets.vst.logic
import org.tygus.suslik.language.Expressions.{Expr, NilPtr, Subst, SubstVar, Var}
import org.tygus.suslik.language.{PrettyPrinting, SSLType, Statements}
import org.tygus.suslik.language.Statements.{Load, Skip, Store}
import org.tygus.suslik.logic.Specifications.Assertion
import org.tygus.suslik.logic.{Heaplet, PFormula, PointsTo, SApp, SFormula, Specifications}
import org.tygus.suslik.synthesis.rules.{DelegatePureSynthesis, FailRules, LogicalRules, OperationalRules, UnificationRules}
import org.tygus.suslik.synthesis.{AppendProducer, BranchProducer, ChainedProducer, ConstProducer, ExtractHelper, GhostSubstProducer, GuardedProducer, HandleGuard, IdProducer, PartiallyAppliedProducer, PrependFromSketchProducer, PrependProducer, SeqCompProducer, StmtProducer, SubstProducer, UnfoldProducer}



/** compressed form of suslik rules */
sealed abstract class ProofRule extends PrettyPrinting {

}

object ProofRule {
  var indent : Int = 0

  def ind : String = " " * indent

  def sanitize (str: String) = str.replace(";\n","")

  def with_scope[A] (f: Unit => A) : A = {
    val old_indent_value = indent
    indent = indent + 4
    val result = f(())
    indent = old_indent_value
    result
  }


  /** corresponds to asserting all the variables in vars are not null */
  case class NilNotLval(vars: List[Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}NilNotLval(${vars.map(_.pp).mkString(", ")});\n${next.pp}"
  }

  /** check post doesn't provide any information useful for certification, so just included as empty rule */
  case class CheckPost(next:ProofRule) extends ProofRule {
    override def pp: String = s"${ind}CheckPost;\n${next.pp}"
  }

  /** picks an arbitrary instantiation of the proof rules */
  case class Pick(subst: Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Pick(${subst.mkString(", ")});\n${next.pp}"
  }

  /** abduces a condition for the proof */
  case class AbduceBranch(cond: Expr, ifTrue:ProofRule, ifFalse:ProofRule) extends ProofRule {
    override def pp: String = s"${ind}AbduceBranch(${cond});\n${ind}IfTrue:\n${with_scope(_ => ifTrue.pp)}\n${ind}IfFalse:\n${with_scope(_ => ifFalse.pp)}"
  }

  /** write a value */
  case class Write(stmt: Store, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Write(${sanitize(stmt.pp)});\n${next.pp}"
  }

  /** weaken the precondition by removing unused formulae */
  case class WeakenPre(unused: PFormula, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}WeakenPre(${unused.pp});\n${next.pp}"
  }

  /** empty rule */
  case object EmpRule extends ProofRule {
    override def pp: String = s"${ind}EmpRule;"
  }

  /** pure synthesis rules */
  case class PureSynthesis(is_final: Boolean, assignments:Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}PureSynthesis(${is_final}, ${assignments.mkString(",")});\n${next.pp}"
  }

  /** open constructor cases */
  case class Open(pred: SApp, fresh_vars: SubstVar, cases: List[(Expr, ProofRule)]) extends ProofRule {
    override def pp: String = s"${ind}Open(${pred.pp}, ${fresh_vars.mkString(", ")});\n${with_scope(_ => cases.map({case (expr,rest) => s"${ind}if ${sanitize(expr.pp)}:\n${with_scope(_ => rest.pp)}"}).mkString("\n"))}"
  }

  /** subst L */
  case class SubstL(map: Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}SubstL(${map.mkString(",")});\n${next.pp}"
  }

  /** subst R */
  case class SubstR(map: Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}SubstR(${map.mkString(",")});\n${next.pp}"
  }


  /** read rule */
  case class Read(map: Map[Var,Expr], operation: Load, next:ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Read(${map.mkString(",")}, ${sanitize(operation.pp)});\n${next.pp}"
  }

//  /** abduce a call */
case class AbduceCall(
                       new_vars: Map[Var, SSLType],
                       f_pre: Specifications.Assertion,
                       callePost: Specifications.Assertion,
                       call: Statements.Call,
                       freshSub: SubstVar,
                       next: ProofRule
                     ) extends ProofRule {
  override def pp: String = s"${ind}AbduceCall({${new_vars.mkString(",")}}, ${sanitize(f_pre.pp)}, ${sanitize(callePost.pp)}, ${sanitize(call.pp)}, {${freshSub.mkString(",")}});\n${next.pp}"
}


  /** unification of heap (ignores block/pure distinction) */
  case class HeapUnify(next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}HeapUnify;\n${next.pp}"
  }

  /** unification of pointers */
  case class HeapUnifyPointer(map: Map[Var,Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}HeapUnifyPointer(${map.mkString(",")});\n${next.pp}"
  }

  /** unfolds frame */
  case class FrameUnfold(h_pre: Heaplet, h_post: Heaplet, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}FrameUnfold(${h_pre.pp}, ${h_post.pp});\n${next.pp}"
  }

  /** call operation */
  case class Call(call: Statements.Call, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Call(${sanitize(call.pp)});\n${next.pp}"
  }

  /** free operation */
  case class Free(stmt: Statements.Free, size: Int, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Free(${sanitize(stmt.pp)});\n${next.pp}"
  }

  /** malloc rule */
  case class Malloc(map: SubstVar, stmt: Statements.Malloc, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Malloc(${map.mkString(",")}, ${sanitize(stmt.pp)});\n${next.pp}"
  }

  /** close rule */
  case class Close(app: SApp, selector: Expr, asn: Assertion, fresh_exist: SubstVar, next: ProofRule) extends  ProofRule {
    override def pp: String = s"${ind}Close(${app.pp}, ${sanitize(selector.pp)}, ${asn.pp}, {${fresh_exist.mkString(",")}});\n${next.pp}"
  }

  /** star partial */
  case class StarPartial(new_pre_phi: PFormula, new_post_phi: PFormula, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}StarPartial(${new_pre_phi.pp}, ${new_post_phi.pp});\n${next.pp}"
  }

  case class PickCard(next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}PickCard;\n${next.pp}"
  }


  case class PickArg(map: Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}PickArg(${map.mkString(",")});\n${next.pp}"
  }


}