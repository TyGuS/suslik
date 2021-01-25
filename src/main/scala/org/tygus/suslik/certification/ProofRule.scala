package org.tygus.suslik.certification

import org.tygus.suslik.certification.targets.vst.translation.ProofTranslation.ProofRuleTranslationException
import org.tygus.suslik.language.Expressions.{Expr, NilPtr, Subst, SubstVar, Var}
import org.tygus.suslik.language.Statements.{Error, Load, Skip, Store}
import org.tygus.suslik.language.{PrettyPrinting, SSLType, Statements}
import org.tygus.suslik.logic.Preprocessor.{findMatchingHeaplets, sameLhs}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal, SuspendedCallGoal}
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis.rules.LogicalRules.StarPartial.extendPure
import org.tygus.suslik.synthesis.rules._
import org.tygus.suslik.synthesis._

import scala.collection.immutable.Map



/** compressed form of suslik rules */
sealed trait ProofRule extends PrettyPrinting {
  def next: List[ProofRule]
}

object ProofRule {
  var indent : Int = 0

  def ind : String = " " * indent

  def sanitize (str: String) = str.replace(";\n","")

  def with_scope[A] (f: Unit => A) : A = {
    val old_indent_value = indent
    indent = indent + 4
    val result = f(())
    indent = old_indent_value
    result
  }


  /** corresponds to asserting all the variables in vars are not null */
  case class NilNotLval(vars: List[Expr], next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}NilNotLval(${vars.map(_.pp).mkString(", ")});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** solves a pure entailment with SMT */
  case class CheckPost(prePhi: PFormula, postPhi: PFormula, next_rule:ProofRule) extends ProofRule {
    override def pp: String = s"${ind}CheckPost(${prePhi.pp}; ${postPhi.pp});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** picks an arbitrary instantiation of the proof rules */
  case class Pick(subst: Map[Var, Expr], next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Pick(${subst.mkString(", ")});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** abduces a condition for the proof */
  case class AbduceBranch(cond: Expr, ifTrue:ProofRule, ifFalse:ProofRule) extends ProofRule {
    override def pp: String = s"${ind}AbduceBranch(${cond});\n${ind}IfTrue:\n${with_scope(_ => ifTrue.pp)}\n${ind}IfFalse:\n${with_scope(_ => ifFalse.pp)}"
    override def next: List[ProofRule] = List(ifTrue, ifFalse)
  }

  /** write a value */
  case class Write(stmt: Store, next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Write(${sanitize(stmt.pp)});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** weaken the precondition by removing unused formulae */
  case class WeakenPre(unused: PFormula, next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}WeakenPre(${unused.pp});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** empty rule */
  case object EmpRule extends ProofRule {
    override def pp: String = s"${ind}EmpRule;"
    override def next: List[ProofRule] = List()
  }

  /** pure synthesis rules */
  case class PureSynthesis(is_final: Boolean, assignments:Map[Var, Expr], next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}PureSynthesis(${is_final}, ${assignments.mkString(",")});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** open constructor cases */
  case class Open(pred: SApp, fresh_vars: SubstVar, sbst: Subst, cases: List[(Expr, ProofRule)]) extends ProofRule {
    override def pp: String = s"${ind}Open(${pred.pp}, ${fresh_vars.mkString(", ")});\n${with_scope(_ => cases.map({case (expr,rest) => s"${ind}if ${sanitize(expr.pp)}:\n${with_scope(_ => rest.pp)}"}).mkString("\n"))}"
    override def next: List[ProofRule] = cases.map({ case (_, rule) => rule })
  }

  /** subst L */
  case class SubstL(map: Map[Var, Expr], next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}SubstL(${map.mkString(",")});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** subst R */
  case class SubstR(map: Map[Var, Expr], next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}SubstR(${map.mkString(",")});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }


  /** read rule */
  case class Read(map: Map[Var,Var], operation: Load, next_rule:ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Read(${map.mkString(",")}, ${sanitize(operation.pp)});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

//  /** abduce a call */
case class AbduceCall(
                       new_vars: Map[Var, SSLType],
                       f_pre: Specifications.Assertion,
                       callePost: Specifications.Assertion,
                       call: Statements.Call,
                       freshSub: SubstVar,
                       freshToActual: Subst,
                       f: FunSpec,
                       gamma: Gamma,
                       next_rule: ProofRule
                     ) extends ProofRule {
  override def pp: String = s"${ind}AbduceCall({${new_vars.mkString(",")}}, ${sanitize(f_pre.pp)}, ${sanitize(callePost.pp)}, ${sanitize(call.pp)}, {${freshSub.mkString(",")}});\n${next_rule.pp}"
  override def next: List[ProofRule] = List(next_rule)
}


  /** unification of heap (ignores block/pure distinction) */
  case class HeapUnify(subst: Map[Var, Expr], next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}HeapUnify(${subst.mkString(",")});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** unification of pointers */
  case class HeapUnifyPointer(map: Map[Var,Expr], next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}HeapUnifyPointer(${map.mkString(",")});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** unfolds frame */
  case class FrameUnfold(h_pre: Heaplet, h_post: Heaplet, next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}FrameUnfold(${h_pre.pp}, ${h_post.pp});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** call operation */
  case class Call(subst: Map[Var, Expr], call: Statements.Call, next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Call({${subst.mkString(",")}}, ${sanitize(call.pp)});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** free operation */
  case class Free(stmt: Statements.Free, size: Int, next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Free(${sanitize(stmt.pp)});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** malloc rule */
  case class Malloc(map: SubstVar, stmt: Statements.Malloc, next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Malloc(${map.mkString(",")}, ${sanitize(stmt.pp)});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** close rule */
  case class Close(app: SApp, selector: Expr, asn: Assertion, fresh_exist: SubstVar, next_rule: ProofRule) extends  ProofRule {
    override def pp: String = s"${ind}Close(${app.pp}, ${sanitize(selector.pp)}, ${asn.pp}, {${fresh_exist.mkString(",")}});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  /** star partial */
  case class StarPartial(new_pre_phi: PFormula, new_post_phi: PFormula, next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}StarPartial(${new_pre_phi.pp}, ${new_post_phi.pp});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  case class PickCard(map: Map[Var,Expr], next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}PickCard(${map.mkString(",")});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }


  case class PickArg(map: Map[Var, Expr], next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}PickArg(${map.mkString(",")});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  case class Init(goal: Goal, next_rule: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Init(${goal.pp});\n${next_rule.pp}"
    override def next: List[ProofRule] = List(next_rule)
  }

  case object Inconsistency extends ProofRule {
    override def pp: String = "Inconsistency"
    override def next: List[ProofRule] = List()
  }

  /**
    * Abstract class for traversing and manipulating proof tree structures.
    *
    * override map_next, map_if_true, map_if_false, map_cases to handle mapping next
    */
  abstract class ProofRuleMapper {

     def map (rule: NilNotLval) =
      NilNotLval(rule.vars, map_next(rule.next_rule))

     def map (rule: CheckPost) =
      CheckPost(rule.prePhi, rule.postPhi, map_next(rule.next_rule))

     def map(rule: Pick)  =
      Pick(rule.subst, map_next(rule.next_rule))

     def map(rule: AbduceBranch) =
      AbduceBranch(rule.cond, map_if_true(rule.ifTrue), map_if_false(rule.ifFalse))

     def map(rule: Write) =
      Write(rule.stmt, map_next(rule.next_rule))

     def map(rule: WeakenPre) =
      WeakenPre(rule.unused, map_next(rule.next_rule))

     def map_emp = EmpRule

     def map (rule: PureSynthesis) =
      PureSynthesis(rule.is_final, rule.assignments, map_next(rule.next_rule))

     def map (rule: Open) =
      Open(rule.pred, rule.fresh_vars, rule.sbst, map_cases(rule.cases))

     def map(rule: SubstL) =
      SubstL(rule.map, map_next(rule.next_rule))

     def map(rule: SubstR) =
      SubstR(rule.map, map_next(rule.next_rule))

     def map(rule: Read) =
      Read(rule.map, rule.operation, map_next(rule.next_rule))

     def map(rule: AbduceCall) =
      AbduceCall(rule.new_vars, rule.f_pre, rule.callePost, rule.call, rule.freshSub, rule.freshToActual, rule.f, rule.gamma, map_next(rule.next_rule))

     def map(rule: HeapUnify) =
      HeapUnify(rule.subst, map_next(rule.next_rule))

     def map(rule: HeapUnifyPointer) =
      HeapUnifyPointer(rule.map, map_next(rule.next_rule))

     def map(rule: FrameUnfold) =
      FrameUnfold(rule.h_pre, rule.h_post, map_next(rule.next_rule))

     def map(rule: Call) =
      Call(rule.subst, rule.call, map_next(rule.next_rule))

     def map(rule: Free) =
      Free(rule.stmt, rule.size, map_next(rule.next_rule))

     def map(rule: Malloc) =
      Malloc(rule.map, rule.stmt, map_next(rule.next_rule))

     def map(rule: Close) =
      Close(rule.app, rule.selector, rule.asn, rule.fresh_exist, map_next(rule.next_rule))

     def map(rule: StarPartial) =
      StarPartial(rule.new_pre_phi, rule.new_post_phi, map_next(rule.next_rule))

     def map(rule: PickCard) =
      PickCard(rule.map, map_next(rule.next_rule))

     def map(rule: PickArg) =
      PickArg(rule.map, map_next(rule.next_rule))

     def map(rule: Init) =
      Init(rule.goal, map_next(rule.next_rule))

     def map_inconsistency = Inconsistency

    def map(rule: ProofRule) : ProofRule = rule match {
      case rule@NilNotLval(_, _) => map(rule)
      case rule@CheckPost(_, _, _) => map(rule)
      case rule@Pick(_, _) => map(rule)
      case rule@AbduceBranch(_, _, _) => map(rule)
      case rule@Write(_, _) => map(rule)
      case rule@WeakenPre(_, _) => map(rule)
      case rule@EmpRule => map_emp
      case rule@PureSynthesis(_, _, _) => map(rule)
      case rule@Open(_, _, _, _) => map(rule)
      case rule@SubstL(_, _) => map(rule)
      case rule@SubstR(_, _) => map(rule)
      case rule@Read(_, _, _) => map(rule)
      case rule@AbduceCall(_, _, _, _, _, _, _, _, _) => map(rule)
      case rule@HeapUnify(_, _) => map(rule)
      case rule@HeapUnifyPointer(_, _) => map(rule)
      case rule@FrameUnfold(_, _, _) => map(rule)
      case rule@Call(_, _, _) => map(rule)
      case rule@Free(_, _, _) => map(rule)
      case rule@Malloc(_, _, _) => map(rule)
      case rule@Close(_, _, _, _, _) => map(rule)
      case rule@StarPartial(_, _, _) => map(rule)
      case rule@PickCard(_, _) => map(rule)
      case rule@PickArg(_, _) => map(rule)
      case rule@Init(_, _) => map(rule)
      case Inconsistency => map_inconsistency
    }

    /***
      * DO NOT CALL THIS FROM CLIENT CODE!!!!
      */
    def map_next(rule: ProofRule): ProofRule
    def map_if_true(rule: ProofRule) : ProofRule
    def map_if_false(rule: ProofRule) : ProofRule

    def map_cases(cases: List[(Expr, ProofRule)]) : List[(Expr, ProofRule)]

  }

  def copy_proof_rule_with_next(rule: ProofRule, next: List[ProofRule]) = {
    class ProofRuleCopy extends ProofRuleMapper {
      override def map_next(rule: ProofRule): ProofRule = {assert(next.length == 1, "Expecting arity of 1"); next.head }
      override def map_if_true(rule: ProofRule): ProofRule = {assert(next.length == 2, "Expecting arity of 2"); next(0) }
      override def map_if_false(rule: ProofRule): ProofRule = {assert(next.length == 2, "Expecting arity of 2"); next(1) }
      override def map_cases(cases: List[(Expr, ProofRule)]): List[(Expr, ProofRule)] = {
        assert(next.length == cases.length, s"Expecting arity of ${cases.length}")
        cases.zip(next).map({case ((expr, _), next) => (expr, next)})
      }
    }

    val mapper = new ProofRuleCopy()
    mapper.map(rule)
  }

  /** converts a Suslik CertTree node into the unified ProofRule structure */
  def of_certtree(node: CertTree.Node): ProofRule = {
    def fail_with_bad_proof_structure(): Nothing =
      throw ProofRuleTranslationException(s"continuation for ${node.rule} is not what was expected: ${node.kont.toString}")
    def fail_with_bad_children(ls: Seq[CertTree.Node], count: Int): Nothing =
      throw ProofRuleTranslationException(s"unexpected number of children for proof rule ${node.rule} - ${ls.length} != $count")

    node.rule match {
      case LogicalRules.NilNotLval => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(_)) =>
          // find all pointers that are not yet known to be non-null
          def find_pointers(p: PFormula, s: SFormula): Set[Expr] = {
            // All pointers
            val allPointers = (for (PointsTo(l, _, _) <- s.chunks) yield l).toSet
            allPointers.filter(
              x => !p.conjuncts.contains(x |/=| NilPtr) && !p.conjuncts.contains(NilPtr |/=| x)
            )
          }

          val pre_pointers = find_pointers(node.goal.pre.phi, node.goal.pre.sigma).toList

          node.children match {
            case ::(head, Nil) => ProofRule.NilNotLval(pre_pointers, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case FailRules.CheckPost => node.kont match {
        case ChainedProducer(PureEntailmentProducer(prePhi, postPhi), IdProducer) => node.children match {
          case ::(head, Nil) => ProofRule.CheckPost(prePhi, postPhi, of_certtree(head))
          case ls => fail_with_bad_children(ls, 1)
        }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.Pick => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.Pick(map, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case FailRules.AbduceBranch => node.kont match {
        case GuardedProducer(cond, _) =>
          node.children match {
            case ::(if_true, ::(if_false, Nil)) => ProofRule.AbduceBranch(cond, of_certtree(if_true), of_certtree(if_false))
            case ls => fail_with_bad_children(ls, 2)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.WriteRule => node.kont match {
        case ChainedProducer(ChainedProducer(PrependProducer(stmt@Store(_, _, _)), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.Write(stmt, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.Inconsistency => node.kont match {
        case ConstProducer(Error) =>
          node.children match {
            case Nil => ProofRule.Inconsistency
            case ls => fail_with_bad_children(ls, 0)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.WeakenPre => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          val unused = goal.pre.phi.indepedentOf(goal.pre.sigma.vars ++ goal.post.vars)
          node.children match {
            case ::(head, Nil) => ProofRule.WeakenPre(unused, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.EmpRule => node.kont match {
        case ConstProducer(Skip) =>
          node.children match {
            case Nil => ProofRule.EmpRule
            case ls => fail_with_bad_children(ls, 0)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case DelegatePureSynthesis.PureSynthesisFinal => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(assignments), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) =>
              ProofRule.PureSynthesis(is_final = true, assignments, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.Open => node.kont match {
        case ChainedProducer(ChainedProducer(BranchProducer(Some(pred), fresh_vars, sbst, selectors), HandleGuard(_)), ExtractHelper(_)) =>
          ProofRule.Open(pred, fresh_vars, sbst, selectors.zip(node.children).map({ case (expr, node) => (expr, of_certtree(node)) }).toList)
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.SubstLeft => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.SubstL(map, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.SubstRight => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.SubstR(map, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.ReadRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(GhostSubstProducer(map), PrependProducer(stmt@Load(_, _, _, _))), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.Read(map, stmt, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.AbduceCall => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(AbduceCallProducer(f), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) =>
              // find out which new variables were added to the context
              val new_vars =
                head.goal.gamma.filterKeys(key => !node.goal.gamma.contains(key))
              val f_pre = head.goal.post
              var SuspendedCallGoal(caller_pre, caller_post, callePost, call, freshSub, freshToActual) = head.goal.callGoal.get
              ProofRule.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, head.goal.gamma, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyPure => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.HeapUnify(subst, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyUnfolding => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.HeapUnify(subst, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyBlock => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.HeapUnify(subst, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyPointer => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.HeapUnifyPointer(subst, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.FrameUnfolding => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              val pre = goal.pre
              val post = goal.post

              def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && LogicalRules.FrameUnfolding.heapletFilter(hPost)

              findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
                case None => ???
                case Some((h_pre, h_post)) =>
                  ProofRule.FrameUnfold(h_pre, h_post, of_certtree(head))
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.FrameUnfoldingFinal => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              val pre = goal.pre
              val post = goal.post

              def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && LogicalRules.FrameUnfoldingFinal.heapletFilter(hPost)

              findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
                case None => ???
                case Some((h_pre, h_post)) =>
                  ProofRule.FrameUnfold(h_pre, h_post, of_certtree(head))
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.FrameBlock => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              val pre = goal.pre
              val post = goal.post

              def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && LogicalRules.FrameBlock.heapletFilter(hPost)

              findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
                case None => ???
                case Some((h_pre, h_post)) =>
                  ProofRule.FrameUnfold(h_pre, h_post, of_certtree(head))
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.FrameFlat => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              val pre = goal.pre
              val post = goal.post

              def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && LogicalRules.FrameFlat.heapletFilter(hPost)

              findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
                case None => ???
                case Some((h_pre, h_post)) =>
                  ProofRule.FrameUnfold(h_pre, h_post, of_certtree(head))
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.CallRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst),PrependProducer(call: Statements.Call)), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.Call(subst, call, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.FreeRule => node.kont match {
        case ChainedProducer(ChainedProducer(PrependProducer(stmt@Statements.Free(Var(name))), HandleGuard(_)), ExtractHelper(_)) =>
          val size: Int = node.goal.pre.sigma.blocks.find({ case Block(Var(ploc), sz) => ploc == name }).map({ case Block(_, sz) => sz }) match {
            case Some(value) => value
            case None => 1
          }
          node.children match {
            case ::(head, Nil) => ProofRule.Free(stmt, size, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.AllocRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(GhostSubstProducer(map), PrependProducer(stmt@Statements.Malloc(_, _, _))), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              ProofRule.
                Malloc(map, stmt, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.Close => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(UnfoldProducer(app, selector, asn, fresh_exist), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) =>
              ProofRule.Close(app, selector, asn, fresh_exist, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
      }
      case LogicalRules.StarPartial => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          val new_pre_phi = extendPure(goal.pre.phi, goal.pre.sigma)
          val new_post_phi = extendPure(goal.pre.phi && goal.post.phi, goal.post.sigma)

          node.children match {
            case ::(head, Nil) =>
              ProofRule.StarPartial(new_pre_phi, new_post_phi, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }

      case UnificationRules.PickCard => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.PickCard(map, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
      }
      case UnificationRules.PickArg => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => ProofRule.PickArg(map, of_certtree(head))
            case ls => fail_with_bad_children(ls, 1)
          }
      }
    }
  }
}