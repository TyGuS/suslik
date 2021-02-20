package org.tygus.suslik.certification.translation

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.{BoolType, Ident, SSLType}
import org.tygus.suslik.logic.{Environment, Heaplet, InductiveClause, InductivePredicate}

abstract class PredicateTranslation[Pure, Spatial, Type,
  Clause <: GenericPredicateClause[Pure, Spatial],
  Pred <: GenericPredicate[Pure, Spatial, Type]] {

  def constructClause(pure: List[Pure], spatial: List[Spatial], subConstructor: Map[String, CardConstructor]) : Clause

  def constructPred(name: Ident, params: List[(Ident, Type)],
                    existentials: List[(Ident, Type)],
                    clauses: Map[CardConstructor, Clause]) : Pred

  def translatePredicateParamType(predName: String, t: SSLType): Type

  def translateExpression(context: Map[Ident, Type])(expr: Expr): Pure

  def translateHeaplets(context: Map[Ident, Type])(heaplets: List[Heaplet]): List[Spatial]

  def translatePredicate(env: Environment)(predicate: InductivePredicate): Pred = {
    // Determines whether a given variable is a cardinality constraint
    def isCard(s: String): Boolean = s.startsWith("_") || s.contentEquals("self_card")

    // extracts a cardinality relation from an expression if it exists
    def extractCardConstructor(expr: Expr): Option[(String, String)] = {
      expr match {
        case BinaryExpr(op, Var(left), Var(parent))
          if isCard(left) && isCard(parent) =>
          op match {
            case op: RelOp => op match {
              case OpLt =>
                Some((left, parent))
              case _ => None
            }
            case _ => None
          }
        case OverloadedBinaryExpr(overloaded_op, Var(left), Var(parent))
          if isCard(left) && isCard(parent) =>
          overloaded_op match {
            case op: BinOp => op match {
              case op: RelOp => op match {
                case OpLt => Some((left, parent))
                case _ => None
              }
              case _ => None
            }
            case OpGt => Some((parent, left))
            case _ => None
          }
        case _ => None
      }
    }

    // base context contains type information for every variable used in the
    // predicate (even if it occurs at a top level or not)
    val (predName: Ident, baseContext: List[(Ident, Type)]) = {
      val (predName, gamma) = predicate match {
        case InductivePredicate(name, params, clauses) =>
          val gamma = clauses.foldLeft(params.toMap)({ case (baseGamma, InductiveClause(selector, asn)) =>
            var gamma = selector.resolve(baseGamma, Some(BoolType)).getOrElse(baseGamma) ++ baseGamma
            gamma = asn.phi.conjuncts.foldLeft(gamma)({ case (gamma, expr) => expr.resolve(gamma, Some(BoolType)).getOrElse(gamma) }) ++ baseGamma
            asn.sigma.resolve(gamma, env).getOrElse(gamma) ++ baseGamma
          })
          (name, gamma)
      }
      (predName, gamma.map({ case (Var(name), ty) => (name, translatePredicateParamType(predName, ty)) }).toList)
    }

    predicate match {
      case InductivePredicate(name, raw_params, raw_clauses) =>
        val params: List[(String, Type)] =
          raw_params.map({ case (Var(name), sType) => (name, translatePredicateParamType(predName, sType)) })
        val context: Map[Ident, Type] = (baseContext ++ params).toMap

        // separate clauses by cardinality constructors
        // NOTE: here we assume that cardinality constructors are unique - i.e each clause maps to a
        // unique cardinality constraint
        val clauses: Map[CardConstructor, Clause] = raw_clauses.map({
          case InductiveClause(selector, asn) =>
            // first, split the pure conditions in the predicate between those that
            // encode cardinality constraints and those that don't
            val (r_conds, r_card_conds) = asn.phi.conjuncts.map(expr =>
              extractCardConstructor(expr) match {
                case value@Some(_) => (None, value)
                case None => (Some(expr), None)
              }
            ).toList.unzip

            // translate the pure conditions
            val select = translateExpression(context)(selector)
            val conds = r_conds.flatten.map(v => translateExpression(context)(v))

            // translate the spatial constraints
            val spat_conds = translateHeaplets(context)(asn.sigma.chunks)

            // Convert the cardinality constraints into an associated constructor
            val card_conds = r_card_conds.flatten
            card_conds match {
              case card_conds@(::(_, _)) =>
                val card_cons: Map[String, CardConstructor] = buildCardCons(card_conds)
                (card_cons("self_card"), constructClause(select :: conds, spat_conds, card_cons))
              case Nil => (CardNull, constructClause(select :: conds, spat_conds, Map.empty))
            }
        }).toMap
        constructPred(name, params, baseContext, clauses)
    }
  }

  /** convert a list of cardinality relations (child, parent) (i.e child < parent) into a map
    * from cardinality name to constructors */
  def buildCardCons(cardConds: List[(String, String)]): Map[String, CardOf] = {
    // to perform this translation, we first construct a mapping of relations
    // where for every constraint of the form (a < b), we set map(b) = a :: map(b),
    // thus the mapping for a variable contains the list of other variables that are
    // constrainted to be immediately smaller than it
    var childMap: Map[String, List[String]] = Map.empty
    cardConds.foreach({ case (child, parent) =>
      childMap.get(parent) match {
        case None => childMap = childMap.updated(parent, List(child))
        case Some(children) => childMap = childMap.updated(parent, child :: children)
      }
    })
    // the keys of the map now become variables that are destructured
    // in the match case to produce the variables immediately below it
    childMap.map({ case (str, strings) => (str, CardOf(strings)) })
  }
}
