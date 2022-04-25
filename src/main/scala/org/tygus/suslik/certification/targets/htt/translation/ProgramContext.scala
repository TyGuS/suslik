package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.targets.htt.program.Statements.CStatement
import org.tygus.suslik.certification.traversal.Evaluator.ClientContext
import org.tygus.suslik.logic.Environment

case class ProgramContext(env: Environment) extends ClientContext[CStatement]
