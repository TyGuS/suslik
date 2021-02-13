package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.targets.htt.program.Statements.CStatement
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext

case class ProgramContext() extends ClientContext[CStatement]
