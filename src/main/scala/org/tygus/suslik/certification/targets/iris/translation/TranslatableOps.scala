package org.tygus.suslik.certification.targets.iris.translation

object TranslatableOps {
  implicit class Translatable[A](value: A) {
    def translate[B](implicit translator: IrisTranslator[A,B], ctx: Option[TranslationContext] = None): B = {
      translator.translate(value, ctx)
    }
  }
}
