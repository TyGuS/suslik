package org.tygus.suslik.certification.targets.iris.translation

object TranslatableOps {
  implicit class Translatable[A](value: A) {
    def translate[B](implicit translator: IrisTranslator[A,B]): B = {
      translator.translate(value)
    }
  }
}
