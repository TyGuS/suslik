package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.synthesis.CertificationBenchmarks

object VSTCertificationBenchmarks extends CertificationBenchmarks {

  val target: CertificationTarget = VST()

  def main(args: Array[String]): Unit = {
    initLog()
    runAllTestsFromDir("certification/dll")
    runAllTestsFromDir("certification/tree")
    runAllTestsFromDir("certification/sll")
    runAllTestsFromDir("certification/sll-bounds")
    runAllTestsFromDir("certification/ints")
    runAllTestsFromDir("certification/bst")
    runAllTestsFromDir("certification/srtl")
  }
}
