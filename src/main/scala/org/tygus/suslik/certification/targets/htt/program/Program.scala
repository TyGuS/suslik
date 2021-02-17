package org.tygus.suslik.certification.targets.htt.program

import org.tygus.suslik.certification.targets.htt.language.CFormals
import org.tygus.suslik.certification.targets.htt.language.Types.HTTType
import org.tygus.suslik.certification.targets.htt.program.Statements.CStatement
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.language.PrettyPrinting

case class Program(name: String, tp: HTTType, formals: CFormals, body: ProofTree[CStatement]) extends PrettyPrinting {
  override def pp: String =
    s"""Program Definition $name : ${name}_type :=
       |  Fix (fun ($name : ${name}_type) vprogs =>
       |    let: (${formals.map(_._1.pp).mkString(", ")}) := vprogs in
       |    Do (
       |      ${ProgramPrinter.pp(body).replace("\n", "\n      ")}
       |    )).""".stripMargin
}
