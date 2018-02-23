package org.tygus.synsl.synthesis

import org.tygus.synsl.SynSLException
import org.tygus.synsl.language.Statements
import org.tygus.synsl.logic._

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait SynthesisRules extends SepLogicUtils {

  val synQualifier : String

  case class SynthesisException(msg: String) extends SynSLException(synQualifier, msg)

  override def _assert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)

  import Statements._

  type Pre = Assertion
  type Post = Assertion

  // A continuation for synthesizing the "larger" statement from substatement
  type StmtProducer = Seq[Statement] => Statement

  abstract sealed class SynthesisRuleResult

  /**
    * Rule is not applicable
    */
  case object SynFail extends SynthesisRuleResult

  /**
    * Rule is applicable and produces:
    * - a sequence of subgoals (premises fo the rule)
    * - a producer: continuation that combines the results of the subgoals into the final statement
    * An empty list of subgoals paired with an constant producer denotes a leaf in the synthesis derivation
    */
  case class SynMoreGoals(goals: Seq[Spec], kont: StmtProducer) extends SynthesisRuleResult

  /**
    * A generic class for a deductive rule to be applied
    */
  abstract class SynthesisRule extends PureLogicUtils {
    // Apply the rule and get the subgoals
    def apply(spec: Spec, env: Environment): SynthesisRuleResult

  }

}
