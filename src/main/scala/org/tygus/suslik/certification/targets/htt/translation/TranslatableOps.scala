package org.tygus.suslik.certification.targets.htt.translation

object TranslatableOps {
  implicit class Translatable[S](value: S) {
    def translate[D](implicit translator: HTTTranslator[S,D]): D = {
      translator.translate(value)
    }
  }
}
