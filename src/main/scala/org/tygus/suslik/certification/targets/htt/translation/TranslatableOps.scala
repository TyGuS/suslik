package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.logic.Environment

object TranslatableOps {
  implicit class Translatable[S](value: S) {
    def translate[D](implicit translator: HTTTranslator[S,D], env: Environment): D = {
      translator.translate(value)
    }
  }
}
