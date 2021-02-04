package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Step._

trait Translator[A <: SourceStep[A], B <: DestStep[B]] {
  def translate(value: A): (B, List[Context[B]])
}
