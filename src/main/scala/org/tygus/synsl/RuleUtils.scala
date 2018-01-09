package org.tygus.synsl

import org.tygus.synsl.language.Expressions.{Expr, Var}
import org.tygus.synsl.logic.Specifications

/**
  * @author Ilya Sergey
  */
trait RuleUtils {

  import Specifications._

  def findHeapletFor(x: Ident, off: Int, spec: Spec): SFormula => Boolean = {
    case PointsTo(y, off1, e2) =>
      x == y.name && off == off1 && spec.isConcrete(Var(x)) &&
          e2.vars.forall(v => spec.isConcrete(v))
    case _ => false
  }

  // Utility methods
  private def ptsInPreWithPairInPost(spec: Spec): Set[PointsTo] = {
    val ptsOpts = for (p@PointsTo(x, o, e1) <- spec.pre.sigma.findSubFormula(_.isInstanceOf[PointsTo])) yield {
      val hs2 = spec.post.sigma.findSubFormula(findHeapletFor(x.name, o, spec))

      assert(hs2.size <= 1, s"Post-condition is inconsistent:\n${spec.pp}")
      if (hs2.nonEmpty) {
        val PointsTo(_, _, e2) = hs2.head.asInstanceOf[PointsTo]
        // Ignore bogus writes: let [frame] handle it
        if (!e1.equals(e2)) Some(p) else None
      } else None
    }
    for (po <- ptsOpts if po.nonEmpty) yield po.get
  }

  // Matching (x :-> -) heaplets in pre/post
  def matchingHeaplets(spec: Spec) : Set[(PointsTo, PointsTo)] = {
    for {
      h1@PointsTo(x, ox, _) <- ptsInPreWithPairInPost(spec)
      hs2 = spec.post.sigma.findSubFormula(findHeapletFor(x.name, ox, spec))
      h2@PointsTo(_, _, e2: Expr) = hs2.head
    } yield (h1, h2)
  }

  // Same as matchingHeaplets, but with only concrete stuff in the postcondition
  def heapletsForWrite(spec: Spec) : Set[(PointsTo, PointsTo)] =
    matchingHeaplets(spec).filter(_._2.value.vars.forall(v => spec.isConcrete(v)))

  // Same as matchingHeaplets, but with only for exact heaplets
  def heapletsForFrame(spec: Spec) : Set[(PointsTo, PointsTo)] =
    matchingHeaplets(spec).filter{case (p1, p2) => p1 == p2}

}
