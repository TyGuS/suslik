package org.tygus.suslik.certification.translation

import org.tygus.suslik.certification.Predicate
import org.tygus.suslik.language.{Ident, PrettyPrinting}


/**
  * Abstract constructors mapping cardinality constraints to
  * termination measures in Coq
  */
trait CardConstructor extends PrettyPrinting {
  def rename(renaming: Map[String, String]) = this match {
    case CardNull => CardNull
    case CardOf(args) => CardOf(args.map(v => renaming.getOrElse(v,v)))
    case _ => this
  }

  def constructorArgs: List[Ident] =
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


abstract class GenericPredicateClause[Pure, Spatial](val pure: List[Pure],
                                            val spatial: List[Spatial],
                                            val subConstructor: Map[String, CardConstructor]) {
  val cardinalityParam: String = "self_card"

  def selector: Pure = pure.head
}

abstract class GenericPredicate[Pure, Spatial, Type](val name: Ident,
                                                     val params: List[(Ident, Type)],
                                                     val existentials: List[(Ident, Type)],
                                                     val clauses: Map[CardConstructor, GenericPredicateClause[Pure, Spatial]])
  extends Predicate with PrettyPrinting {

  // When extending GenericPredicate, you should implement these methods
  def ppPredicate: String

  /**
    * For a given clause of the predicate and its associated constructor,
    * return the list of existential variables used in the body of the clause
    *
    * @param cons    a constructor matching some clause of the predicate
    * @param pclause the corresponding clause of the predicate
    * @return the list of pairs of (variable, variable_type) of all the existential variables in this clause
    * */
  def findExistentials(cons: CardConstructor)(pclause: GenericPredicateClause[Pure, Spatial]): List[(Ident, Type)]

  /** formal parameters of the predicate.
    * This is the sequence of identifiers that will need to be passed to the predicate to instantiate it. */
  def formalParams: List[Ident] = params.map({ case (a, _) => a }) ++ List("self_card")

  /**
    * Returns the constructor of the predicate with n arguments
    *
    * @param n number of arguments
    */
  def constructorByArg(n: Int): CardConstructor =
    clauses.find({ case (constructor, clause) => constructor.constructorArgs.length == n }).get._1

  /** returns all instances of constructors and the bindings they expose */
  def constructors: List[CardConstructor] =
    clauses.flatMap({ case (constructor, clause) =>
      constructor :: (clause.subConstructor).toList.map({ case (_, constructor) => constructor })
    }).toList

  /**
    * @param selector a expression corresponding to a selector of the predicate
    * @return cardinality and clause matched by predicate
    */
  def apply(selector: Pure): (CardConstructor, GenericPredicateClause[Pure, Spatial]) =
    clauses.find({ case (_, clause) => clause.selector.equals(selector) }).get

  // This function expands the arguments of a constructor and
  // creates recursive pattern matches if necassary - i.e
  //
  // S ((S b) as a) => .....
  def expandArgs(sub_constructor: Map[String, CardConstructor])(idents: List[Ident]): String = {
    idents.map(arg =>
      sub_constructor.get(arg) match {
        case Some(constructor) =>
          s"(${constructorName(constructor)} ${expandArgs(sub_constructor)(constructor.constructorArgs)} as ${arg})"
        case None => arg
      }
    ).mkString(" ")
  }

  /** returns the existential variables introduced by a constructor invokation */
  def constructorExistentials(constructor: CardConstructor): List[(Ident, Type)] = {
    val predicate = clauses(constructor)
    findExistentials(constructor)(predicate)
  }

  override def pp: String = s"${ppInductive}${ppPredicate}"

  /** pretty print the constructor */
  def ppInductive: String = {
    val constructor_map = baseConstructors.map({
      case CardNull => (0, CardNull)
      case v@CardOf(args) => (args.length, v)
    }).toMap

    def pp_constructor(constructor: CardConstructor) = {
      constructor match {
        case CardNull => s"${constructorName(constructor)} : ${inductiveName}"
        case CardOf(args) =>
          s"${constructorName(constructor)} : ${(args ++ List(inductiveName)).map(_ => inductiveName).mkString(" -> ")}"
      }
    }

    val inductive_definition = {
      s"""Inductive ${inductiveName} : Set :=
           ${
        constructor_map.map({ case (_, constructor) =>
          s"|    | ${pp_constructor(constructor)}"
        }).mkString("\n")
      }.
         |
         |""".stripMargin
    }

    s"${inductive_definition}"
  }

  def constructorName(constructor: CardConstructor): String = {
    val count = constructor match {
      case CardNull => 0
      case CardOf(args) => args.length
    }
    s"${inductiveName}_${count}"
  }

  def inductiveName: String = s"${name}_card"

  /** returns all the constructors used in the base match, assumed to be a superset
    * of the constructors used elsewhere
    *
    * Note: to see how there might be constructors elsewhere, suppose we had a cardinality
    * constraint of the form:
    *
    * - `a < self_card`
    *
    * - `b < a`
    *
    * Then the corresponding match case would look like:
    *
    * `pred_1 ((pred_1 b) as a) => ... `
    *
    * I don't this this actually happens in practice, so this is probably just a bit of
    * over-engineering
    * */
  def baseConstructors: List[CardConstructor] =
    clauses.map({ case (constructor, _) =>
      constructor
    }).toList

}
