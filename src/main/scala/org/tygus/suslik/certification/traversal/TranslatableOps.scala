package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Evaluator._
import org.tygus.suslik.certification.traversal.Step._

object TranslatableOps {
  implicit class Translatable[A <: SourceStep](step: A) {
    def translate[B <: DestStep](clientContext: ClientContext[B])(implicit translator: Translator[A, B]): Translator.Result[B] = {
      translator.translate(step, clientContext)
    }
  }
}
