package org.tygus.suslik.certification.targets.htt

import org.tygus.suslik.certification._
import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.logic.Sentences.CInductivePredicate
import org.tygus.suslik.certification.targets.htt.translation.Translation
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.logic.Specifications.Goal

case class HTT() extends CertificationTarget {
  type T = HTT
  type P = CInductivePredicate
  val name: String = "HTT"
  val suffix: String = ".v"

  def certify(testName: String, proc: Procedure, tree: ProofTree[SuslikProofStep], goal: Goal, env: Environment): HTTCertificate = {
    Translation.translate(testName, tree, goal, proc)(env)
  }

  def generate_common_definitions_of(defFileName: String, predicates: List[CInductivePredicate]): List[CertificateOutput] = {
    List(CoqOutput(defFileName ++ ".v", defFileName, s"${HTT.prelude}\n${predicates.map(_.pp).mkString("\n\n")}"))
  }
}

object HTT {
  val prelude =
    """From mathcomp
      |Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
      |From fcsl
      |Require Import prelude pred pcm unionmap heap.
      |From HTT
      |Require Import stmod stsep stlog stlogR.
      |From SSL
      |Require Import core.
      |From Hammer Require Import Hammer.
      |(* Configure Hammer *)
      |Set Hammer ATPLimit 60.
      |Unset Hammer Eprover.
      |Unset Hammer Vampire.
      |Add Search Blacklist "fcsl.".
      |Add Search Blacklist "HTT.".
      |Add Search Blacklist "Coq.ssr.ssrfun".
      |Add Search Blacklist "mathcomp.ssreflect.ssrfun".
      |Add Search Blacklist "mathcomp.ssreflect.bigop".
      |Add Search Blacklist "mathcomp.ssreflect.choice".
      |Add Search Blacklist "mathcomp.ssreflect.div".
      |Add Search Blacklist "mathcomp.ssreflect.finfun".
      |Add Search Blacklist "mathcomp.ssreflect.fintype".
      |Add Search Blacklist "mathcomp.ssreflect.path".
      |Add Search Blacklist "mathcomp.ssreflect.tuple".
      |
      |""".stripMargin

}