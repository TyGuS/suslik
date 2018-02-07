package org.tygus.synsl

import org.tygus.synsl.language.Expressions.{Expr, Var}
import org.tygus.synsl.logic.Specifications

/**
  * @author Ilya Sergey
  */
trait RuleUtils {

  import Specifications._

  def findHeaplet(p: (Heaplet) => Boolean): SFormula => Option[Heaplet] = sigma => {
    sigma.chunks.find(p)
  }

  def findMatchingHeaplets(pl: Heaplet => Boolean, pr: Heaplet => (Heaplet => Boolean)): (SFormula, SFormula) => Option[(Heaplet, Heaplet)]
    = (pre, post) => {
    val matches = for (hl <- pre.chunks.filter(pl)) yield {
      post.chunks.find(pr(hl)) match {
        case None => None
        case Some(hr) => Some(hl, hr)
      }
    }
    matches.find(_.isDefined).flatten
  }


  def isGhostHeaplet(spec: Spec): Heaplet => Boolean = {
    case PointsTo(_, _, a@(Var(_))) => spec.isGhost(a)
    case _ => false
  }

  def isConcreteHeaplet(spec: Spec): Heaplet => Boolean = {
    case PointsTo(_, _, e) => e.vars.forall(v => spec.isConcrete(v))
    case _ => false
  }

  def sameLhs(hl: Heaplet): Heaplet => Boolean = hr => {
    val pt = hl.asInstanceOf[PointsTo]
    hr match {
      case PointsTo(y, off, _) => pt.id == y && pt.offset == off
      case _ => false
    }
  }
}
