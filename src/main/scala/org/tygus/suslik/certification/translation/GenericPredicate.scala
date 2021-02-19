package org.tygus.suslik.certification.translation

import org.tygus.suslik.language.{Ident, PrettyPrinting}


/**
  * Abstract constructors mapping cardinality constraints to
  * termination measures in Coq
  */
trait CardConstructor extends PrettyPrinting {
  def constructor_args: List[Ident] =
    this match {
      case CardNull => Nil
      case CardOf(args) => args
    }
}

/**
  * Null constructor of 0 cardinality
  */
case object CardNull extends CardConstructor {}

/** Cardinality constructor of multiple components
  *
  * @param args the variables produced by unwrwapping this element
  */
case class CardOf(args: List[Ident]) extends CardConstructor {}


case class GenericPredicateClause[Pure, Spatial](phi: List[Pure],
                                                 sigma: List[Spatial],
                                                 subConstructor: Map[String, CardConstructor])

case class GenericPredicate[Pure, Spatial, Type](name: Ident,
                                                 params: List[(String, Type)],
                                                 existentials: List[(String, Type)],
                                                 clauses: Map[CardConstructor, GenericPredicateClause[Pure, Spatial]])
  extends PrettyPrinting {}
