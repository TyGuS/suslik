package org.tygus.synsl.synthesis.instances

import org.tygus.synsl.synthesis.{SynthesisTests, Synthesis}

/**
  * @author Ilya Sergey
  */

class SimpleSynthesisTests extends SynthesisTests {
  val synthesis: Synthesis = new SimpleSynthesis
}
