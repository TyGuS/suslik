package org.tygus.suslik.certification.targets.iris

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.synthesis.CertificationBenchmarks

object IrisCertificationBenchmarks extends CertificationBenchmarks {
  val target: CertificationTarget = Iris()

  def main(args: Array[String]): Unit = {
    initLog()
    runAllTestsFromDir("certification/ints")
    runAllTestsFromDir("certification/sll")
    runAllTestsFromDir("certification/dll")
    runAllTestsFromDir("certification/tree")
    runAllTestsFromDir("certification/sll-bounds")
    runAllTestsFromDir("certification/srtl")
    runAllTestsFromDir("certification/bst")
  }
}
