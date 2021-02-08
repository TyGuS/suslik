package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator._
import org.tygus.suslik.certification.traversal.Step._

object TranslatableOps {
  implicit class Translatable[A <: SourceStep](step: A) {
    def translate[B <: DestStep, C <: ClientContext[B]](clientContext: C)(implicit translator: Translator[A, B, C]): Translator.Result[B,C] = {
      translator.translate(step, clientContext)
    }
  }
}
