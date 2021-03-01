package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.synthesis.CertificationBenchmarks

object VSTCertificationBenchmarks extends CertificationBenchmarks {

  val target: CertificationTarget = VST()

  def main(args: Array[String]): Unit = {
    initLog()
    runAllTestsFromDir("certification/sll-bounds")
    runAllTestsFromDir("certification/bst")
    runAllTestsFromDir("certification/sll")
    runAllTestsFromDir("certification/tree")
    runAllTestsFromDir("certification/srtl")
    runAllTestsFromDir("certification/dll")
    runAllTestsFromDir("certification/ints")

  }
}
