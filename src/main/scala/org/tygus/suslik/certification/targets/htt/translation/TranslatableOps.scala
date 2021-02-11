package org.tygus.suslik.certification.targets.htt.translation

object TranslatableOps {
  implicit class Translatable[A](value: A) {
    def translate[B](implicit translator: HTTTranslator[A,B]): B = {
      translator.translate(value)
    }
  }
}
