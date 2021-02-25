package org.tygus.suslik.certification.targets.iris.translation

import org.tygus.suslik.certification.targets.iris.heaplang.Types.HType

object TranslatableOps {
  implicit class Translatable[A](value: A) {
    def translate[B](implicit translator: IrisTranslator[A,B], ctx: Option[ProgramTranslationContext] = None, target: Option[HType] = None): B = {
      translator.translate(value, ctx, target)
    }
  }
}
