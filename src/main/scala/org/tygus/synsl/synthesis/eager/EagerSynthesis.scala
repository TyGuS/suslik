package org.tygus.synsl.synthesis.eager

import org.tygus.synsl.synthesis.Synthesis

/**
  * @author Ilya Sergey
  */

class EagerSynthesis extends Synthesis with EagerRules {

  val rulesToApply: List[Rule] = List(EmpRule, FrameRule, ReadRule, WriteRule, FreeRule, AllocRule, OpenRule, CloseRule)
  val maxDepth = 25

}
