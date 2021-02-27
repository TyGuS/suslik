package org.tygus.suslik.certification.targets.iris.logic

import org.tygus.suslik.certification.targets.htt.translation.Translation.TranslationException
import org.tygus.suslik.certification.targets.iris.heaplang.Expressions._
import org.tygus.suslik.certification.targets.iris.heaplang.Types.{HBoolType, HIntSetType, HIntType, HLocType, HType, HValType}
import org.tygus.suslik.certification.translation.{CardConstructor, GenericPredicate, GenericPredicateClause}
import org.tygus.suslik.language.{Ident, PrettyPrinting}

object Assertions {

  /** Unlike HTT, which encodes programs in a shallow embedding, Iris has a deep embedding of programs.
    * As such, program expressions are NOT Iris assertions (phi != HExpr). We define a lifting of
    * program-level expressions to spec-level. */
  abstract class IPureAssertion extends PrettyPrinting {
    def ppAsPhi: String = pp
    def ppAsBool: String = ppAsPhi
    def typ: HType

    def conjuncts: Seq[IPureAssertion] = throw TranslationException("Called conjuncts on IPureAssertion not of type IAnd.")

    // TODO: implement this
    def subst(s: Map[Ident, IPureAssertion]): IPureAssertion = this match {
      case expr => expr
    }

    def rename(s: Map[Ident, Ident]): IPureAssertion = this match {
      case expr@ISpecVar(old, t) => s.get(old) match {
        case Some(newName) => ISpecVar(newName, t)
        case None => expr
      }
      case expr => expr
    }
  }

  abstract class IQuantifiedVar extends IPureAssertion {
    def name: Ident

    def originalName: Ident = throw TranslationException("Called originalName on IQuantifiedVar not of type ISpecQuantifiedValue.")
  }

  abstract class ISpatialAssertion extends PrettyPrinting {

    def heaplets: Seq[ISpatialAssertion] = throw TranslationException("Called heaplets on ISpatialAssertion not of type IHeap.")
  }

  abstract class ISpecification extends PrettyPrinting

  case class ISpecLit(lit: HLit) extends IPureAssertion {
    override def pp: String = lit.pp

    // Don't print the # at the beginning
    override def ppAsPhi: String = pp.substring(1)

    override def typ: HType = HValType()
  }

  case class ISpecMakeVal(v: ISpecVar) extends IPureAssertion {
    override def pp: String = s"#${v.pp}"
    override def typ: HType = HValType()
  }

  case class ISpecVar(name: String, typ: HType) extends IQuantifiedVar {
    override def pp: String = s"${name}"

    override def ppAsPhi: String = super.ppAsPhi
  }

  case class ISpecQuantifiedValue(name: String, override val originalName: Ident, typ: HType) extends IQuantifiedVar {
    override def pp: String = s"${name}"
  }

  case class ISetLiteral(elems: List[IPureAssertion]) extends IPureAssertion {
    override def pp: String =
      s"[${elems.map(_.pp).mkString("; ")}]"

    override def typ: HType = HIntSetType()
  }

  case class ISpecUnaryExpr(op: HUnOp, expr: IPureAssertion) extends IPureAssertion {
    override def pp: String = s"(${op.pp} ${expr.pp})"

    override def ppAsPhi: String = s"${op.pp} ${expr.ppAsPhi}"

    override def typ: HType = op match {
      case HOpUnaryMinus => HIntType()
      case HOpNot => HBoolType()
      case _ => ???
    }
  }

  case class ISpecIfThenElse(cond: IPureAssertion, trueBranch: IPureAssertion, falseBranch: IPureAssertion) extends IPureAssertion {
    override def pp: String = s"if ${cond.pp} then ${trueBranch.pp} else ${falseBranch.pp}"
    override def ppAsPhi: String = s"if ${cond.ppAsBool} then ${trueBranch.ppAsPhi} else ${falseBranch.ppAsPhi}"

    override def typ: HType = trueBranch.typ
  }

  case class ISpecBinaryExpr(op: HBinOp, left: IPureAssertion, right: IPureAssertion) extends IPureAssertion {
    override def pp: String = s"(${left.pp} ${op.pp} ${right.pp})"

    override def ppAsBool: String = op match {
      case HOpLe => s"(Z.leb ${left.ppAsPhi} ${right.ppAsPhi})"
      case HOpLt => s"(Z.ltb ${left.ppAsPhi} ${right.ppAsPhi})"
      case _ => ppAsPhi
    }

    override def ppAsPhi: String = op match {
      case HOpLe | HOpLt | HOpPlus | HOpMinus | HOpMultiply
        if left.typ == HIntType() || right.typ == HIntType()
      => s"(${left.ppAsPhi} ${op.pp} ${right.ppAsPhi})%Z"
      case _ => s"(${left.ppAsPhi} ${op.pp} ${right.ppAsPhi})"
    }

    override def typ: HType = op match {
      case HOpEq | HOpLe | HOpLt => HBoolType()
      case HOpUnion => HIntSetType()
      case HOpPlus | HOpMinus | HOpMultiply => HIntType()
      case HOpOffset => HLocType()
      case _ => ???
    }
  }

  case class IAnd(override val conjuncts: Seq[IPureAssertion]) extends IPureAssertion {
    override def pp: String = s"${conjuncts.map(_.ppAsPhi).mkString(" ∧ ")}"

    override def typ: HType = HBoolType()

  }

  case class IPointsTo(loc: IPureAssertion, value: IPureAssertion) extends ISpatialAssertion {
    override def pp: String = s"${loc.pp} ↦ ${value.pp}"
  }

  case class IPredApp(pred: String, args: Seq[IPureAssertion], card: IPureAssertion) extends ISpatialAssertion {
    override def pp: String =
      s"(${pred} ${(args.map(_.ppAsPhi) ++ List(card.pp)).mkString(" ")})"
  }

  case class IBlock() extends ISpatialAssertion {
    override def pp: String = s"⌜True⌝"
  }

  case class IHeap(override val heaplets: Seq[ISpatialAssertion]) extends ISpatialAssertion {
    override def pp: String = s"${heaplets.map(_.pp).mkString(" ∗ ")}"
  }

  case class IAssertion(phi: IPureAssertion, sigma: ISpatialAssertion) extends PrettyPrinting {
    override def pp: String = {
      val pure = if (phi.ppAsPhi.isEmpty) "" else s"⌜${phi.ppAsPhi}⌝"
      val spatial = sigma.pp
      val whole = s"${pure}${if(pure.nonEmpty && spatial.nonEmpty) " ∗ " else ""}${sigma.pp}"
      if (whole.isEmpty) "True" else whole
    }
  }

  case class IFunSpec(fname: Ident,
                      funArgs: Seq[(ISpecVar, HType)],
                      specUniversal: Seq[(IQuantifiedVar, HType)],
                      specExistential: Seq[(IQuantifiedVar, HType)],
                      pre: IAssertion,
                      post: IAssertion
                     ) extends ISpecification {

    override def pp: String = {
      val postExist =
        if (specExistential.nonEmpty)
          s"∃ ${specExistential.map({ case (v, ty) => s"(${v.pp} : ${ty.pp})"}).mkString(" ")}, "
        else ""

      val universal = specUniversal
      s"""
         |Lemma ${fname}_spec :
         |∀ ${universal.map({ case (v, ty) => s"(${v.pp} : ${ty.pp})"}).mkString(" ")},
         |{{{ ${pre.pp} }}}
         |  ${fname} ${funArgs.map(v => s"#${v._1.pp}").mkString(" ")}
         |{{{ RET #(); ${postExist}${post.pp} }}}.
         |""".stripMargin
    }
  }

  case class IPredicateClause(override val pure: List[IPureAssertion],
                              override val spatial: List[ISpatialAssertion],
                              override val subConstructor: Map[String, CardConstructor])
    extends GenericPredicateClause[IPureAssertion, ISpatialAssertion](pure, spatial, subConstructor)

  case class IPredicate(override val name: Ident,
                        override val params: List[(Ident, HType)],
                        override val existentials: List[(Ident, HType)],
                        override val clauses: Map[CardConstructor, IPredicateClause])
    extends GenericPredicate[IPureAssertion, ISpatialAssertion, HType](name, params, existentials, clauses) {

    abstract class IPredicateHelper extends PrettyPrinting

    case class HelpUnfold(predicate: IPredicate, cardConstructor: CardConstructor, pclause: IPredicateClause) extends IPredicateHelper {
      override def pp: String = {
        s"Lemma ${predicate.openLemmaName(cardConstructor)} " +
          s"${cardConstructor.constructorArgs.map(v => s"(${v} : ${predicate.inductiveName})").mkString(" ")} " +
          s"${predicate.params.map({ case (name, proofType) => s"(${name}: ${proofType.pp})" }).mkString(" ")} " +
          s":\n${predicate.name} ${predicate.params.map(_._1).mkString(" ")} (${predicate.constructorName(cardConstructor)} ${
            predicate.expandArgs(pclause.subConstructor)(cardConstructor.constructorArgs)
          }) = (${predicate.ppConstructorClause(cardConstructor, pclause)})%I.\nProof. auto. Qed.\n"
      }

    }

    def openLemmaName(cardConstructor: CardConstructor): String = s"${constructorName(cardConstructor)}_open"
    def learnLemmaName(cardConstructor: CardConstructor): String = s"${constructorName(cardConstructor)}_learn"

    /*** See the health warnings attached to LocalFacts. The same apply. */
    case class HelpCard(predicate: IPredicate, cardConstructor: CardConstructor, pclause: IPredicateClause) extends IPredicateHelper {
      override def pp: String = {
        def ppPred: String = s"${predicate.name} ${predicate.params.map(_._1).mkString(" ")}"

        def ppEqualityTerm(cons: CardConstructor): String =
          if (cons.constructorArgs.isEmpty) {
            s"${ppPred} ${cardinalityParam} = ${ppPred} ${predicate.constructorName(cons)}"
          } else {
            s"∃ ${cons.constructorArgs.mkString(" ")}, ${ppPred} ${cardinalityParam} = ${ppPred} (${predicate.constructorName(cons)} ${cons.constructorArgs.mkString(" ")})"
          }

        s"Lemma ${predicate.learnLemmaName(cardConstructor)} " +
          s"${predicate.params.map({ case (name, proofType) => s"(${name}: ${proofType.pp})" }).mkString(" ")} " +
          s"${cardinalityParam}:\n" +
          s"${pclause.selector.ppAsPhi} -> ${ppEqualityTerm(cardConstructor)}.\n" +
          s"Proof. Admitted.\n"
      }
    }

    val cardinalityParam: String = "self_card"

    def getHelpers: List[IPredicateHelper] = {
      val cardLemmas = clauses.map({ case (constructor, clause) => HelpCard(this, constructor, clause )})
      val unfoldingLemmas = clauses.map({ case (constructor, clause) => HelpUnfold(this, constructor, clause )})
      cardLemmas.toList ++ unfoldingLemmas.toList
    }

    def ppConstructorClause(constr: CardConstructor, pclause: IPredicateClause): String = {
      val IPredicateClause(pure, spatial, _) = pclause
      val clause = IAssertion(IAnd(pure), IHeap(spatial))
      val ex = findExistentials(constr)(pclause)
      val exStr = if (ex.nonEmpty)  s"∃ ${ex.map({ case (name, ty) => s"($name : ${ty.pp})"}).mkString(" ")}, " else ""
      s"${exStr}${clause.pp}"
    }

    def ppPredicate: String = {
      val predicate_definition =
        s"""Fixpoint ${name} ${params.map({ case (name, proofType) => s"(${name}: ${proofType.pp})" }).mkString(" ")} (${cardinalityParam}: ${inductiveName}) { struct self_card } : iProp Σ := match self_card with
           ${
          clauses.map({ case (constructor, pclause@IPredicateClause(_, _, subConstructor)) =>
            s"|    | ${constructorName(constructor)} ${
              expandArgs(subConstructor)(constructor.constructorArgs)
            } => ${
              ppConstructorClause(constructor, pclause)
            }"
          }).mkString("\n")
        }
           |end.
           |""".stripMargin
      s"${predicate_definition}"
    }

    /**
      * For a given clause of the predicate and its associated constructor,
      * return the list of existential variables used in the body of the clause
      *
      * @param cons    a constructor matching some clause of the predicate
      * @param pclause the corresponding clause of the predicate
      * @return the list of pairs of (variable, variable_type) of all the existential variables in this clause
      * */
    override def findExistentials(cons: CardConstructor)(pclause: GenericPredicateClause[IPureAssertion, ISpatialAssertion]): List[(Ident, HType)] = {
      val paramMap = params.toMap

      //
      val existMap = existentials.toMap
      val cardMap = cons.constructorArgs

      pclause match {
        case IPredicateClause(pure, spatial, subClauses) =>
          val clauseCardMap = (cardMap ++ subClauses.flatMap({ case (_, cons) => cons.constructorArgs })).toSet

          def pureExistentials(exp: IPureAssertion): Set[Ident] = exp match {
            case ISpecVar(name, _) => {
              paramMap.get(name) match {
                // A variable that is neither (1) a parameter of the predicate nor (2) a cardinality IS an existential
                case None if !clauseCardMap.contains(name) => Set(name)
                case _ => Set()
              }
            }
            case ISpecBinaryExpr(_, left, right) => pureExistentials(left) ++ pureExistentials(right)
            case ISpecUnaryExpr(_, expr) => pureExistentials(expr)
            case ISpecIfThenElse(cond, left, right) => pureExistentials(cond) ++ pureExistentials(left) ++ pureExistentials(right)
            case ISetLiteral(elems) => elems.flatMap(pureExistentials).toSet
            case ISpecMakeVal(v) => pureExistentials(v)
            case ISpecLit(_) => Set()
            case _ => ???
          }
          def spatialExistentials(heap: ISpatialAssertion): Set[Ident] = heap match {
            case IPointsTo(loc, value) => pureExistentials(loc) ++ pureExistentials(value)
            case IPredApp(_, args, _) => args.flatMap(pureExistentials).toSet
            case IHeap(heaplets) => heaplets.flatMap(spatialExistentials).toSet
            case IBlock() => Set()
            case _ => ???
          }
          (pure.flatMap(pureExistentials) ++ spatial.flatMap(spatialExistentials)).distinct.map(v => (v, existMap(v)))

      }
    }
  }

}