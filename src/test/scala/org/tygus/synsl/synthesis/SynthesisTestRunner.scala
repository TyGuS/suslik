package org.tygus.synsl.synthesis

import java.lang.Boolean.parseBoolean

import org.tygus.synsl.synthesis.instances.SimpleSynthesis

/**
  * @author Ilya Sergey
  */

object SynthesisTestRunner extends SynthesisTestUtil {
  val synthesis: Synthesis = new SimpleSynthesis

  /**
    * Running a single test file (2nd argument) from a folder (1 argument) under
    * ./src/test/resources/synthesis
    *
    * For instance, you can run from IntelliJ config by passing, e.g.,
    * simple emp
    * as program arguments
    *
    * You can also do it using sbt from the command line (from the project root):
    *
    * sbt "test:runMain org.tygus.synsl.synthesis.SynthesisTestRunner simple write1"
    *
    */
  def main(args: Array[String]): Unit = {
    assert(args.length > 0)
    val dirName = args(0)
    val fileName = args(1)
    val printFails = if (args.length > 2) parseBoolean(args(2)) else true
    // TODO: refactor to pass more parameters as implicits
    val params = TestParams(printFails)
    runSingleTestFromDir(dirName, fileName, params)
  }

  def doTest(desc: String, in: String, out: String, params: TestParams): Unit = {
    println(desc)
    println
    synthesizeFromSpec(in, out, params)
  }
}
