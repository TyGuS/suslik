package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.synthesis.CertificationBenchmarks

object HTTCertificationBenchmarks extends CertificationBenchmarks {
  val targets: List[CertificationTarget] = List(HTT())

  def main(args: Array[String]): Unit = {
    initLog()
    runAllTestsFromDir("certification/ints")
    runAllTestsFromDir("certification/sll-bounds")
    runAllTestsFromDir("certification/sll")
    runAllTestsFromDir("certification/dll")
    runAllTestsFromDir("certification/srtl")
    runAllTestsFromDir("certification/tree")
    runAllTestsFromDir("certification/bst")
  }
}