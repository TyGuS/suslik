package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Step._

object TranslatableOps {
  implicit class Translatable[A <: SourceStep[A]](step: A) {
    def translate[B <: DestStep[B]](implicit translator: Translator[A, B]): (B, List[Context[B]]) = {
      translator.translate(step)
    }
  }
}
