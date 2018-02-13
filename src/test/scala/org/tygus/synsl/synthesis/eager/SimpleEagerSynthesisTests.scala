package org.tygus.synsl.synthesis.eager

import org.tygus.synsl.synthesis.{SimpleSynthesisTests, Synthesis}

/**
  * @author Ilya Sergey
  */

class SimpleEagerSynthesisTests extends SimpleSynthesisTests {
  val synthesis: Synthesis = new EagerSynthesis
}
