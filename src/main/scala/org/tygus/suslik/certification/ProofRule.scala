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
sealed abstract class ProofRule extends PrettyPrinting {

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
  case class NilNotLval(vars: List[Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}NilNotLval(${vars.map(_.pp).mkString(", ")});\n${next.pp}"
  }

  /** check post doesn't provide any information useful for certification, so just included as empty rule */
  case class CheckPost(next:ProofRule) extends ProofRule {
    override def pp: String = s"${ind}CheckPost;\n${next.pp}"
  }

  /** picks an arbitrary instantiation of the proof rules */
  case class Pick(subst: Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Pick(${subst.mkString(", ")});\n${next.pp}"
  }

  /** abduces a condition for the proof */
  case class AbduceBranch(cond: Expr, ifTrue:ProofRule, ifFalse:ProofRule) extends ProofRule {
    override def pp: String = s"${ind}AbduceBranch(${cond});\n${ind}IfTrue:\n${with_scope(_ => ifTrue.pp)}\n${ind}IfFalse:\n${with_scope(_ => ifFalse.pp)}"
  }

  /** write a value */
  case class Write(stmt: Store, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Write(${sanitize(stmt.pp)});\n${next.pp}"
  }

  /** weaken the precondition by removing unused formulae */
  case class WeakenPre(unused: PFormula, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}WeakenPre(${unused.pp});\n${next.pp}"
  }

  /** empty rule */
  case object EmpRule extends ProofRule {
    override def pp: String = s"${ind}EmpRule;"
  }

  /** pure synthesis rules */
  case class PureSynthesis(is_final: Boolean, assignments:Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}PureSynthesis(${is_final}, ${assignments.mkString(",")});\n${next.pp}"
  }

  /** open constructor cases */
  case class Open(pred: SApp, fresh_vars: SubstVar, sbst: Subst, cases: List[(Expr, ProofRule)]) extends ProofRule {
    override def pp: String = s"${ind}Open(${pred.pp}, ${fresh_vars.mkString(", ")});\n${with_scope(_ => cases.map({case (expr,rest) => s"${ind}if ${sanitize(expr.pp)}:\n${with_scope(_ => rest.pp)}"}).mkString("\n"))}"
  }

  /** subst L */
  case class SubstL(map: Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}SubstL(${map.mkString(",")});\n${next.pp}"
  }

  /** subst R */
  case class SubstR(map: Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}SubstR(${map.mkString(",")});\n${next.pp}"
  }


  /** read rule */
  case class Read(map: Map[Var,Var], operation: Load, next:ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Read(${map.mkString(",")}, ${sanitize(operation.pp)});\n${next.pp}"
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
                       next: ProofRule
                     ) extends ProofRule {
  override def pp: String = s"${ind}AbduceCall({${new_vars.mkString(",")}}, ${sanitize(f_pre.pp)}, ${sanitize(callePost.pp)}, ${sanitize(call.pp)}, {${freshSub.mkString(",")}});\n${next.pp}"
}


  /** unification of heap (ignores block/pure distinction) */
  case class HeapUnify(subst: Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}HeapUnify(${subst.mkString(",")});\n${next.pp}"
  }

  /** unification of pointers */
  case class HeapUnifyPointer(map: Map[Var,Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}HeapUnifyPointer(${map.mkString(",")});\n${next.pp}"
  }

  /** unfolds frame */
  case class FrameUnfold(h_pre: Heaplet, h_post: Heaplet, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}FrameUnfold(${h_pre.pp}, ${h_post.pp});\n${next.pp}"
  }

  /** call operation */
  case class Call(subst: Map[Var, Expr], call: Statements.Call, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Call({${subst.mkString(",")}}, ${sanitize(call.pp)});\n${next.pp}"
  }

  /** free operation */
  case class Free(stmt: Statements.Free, size: Int, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Free(${sanitize(stmt.pp)});\n${next.pp}"
  }

  /** malloc rule */
  case class Malloc(map: SubstVar, stmt: Statements.Malloc, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Malloc(${map.mkString(",")}, ${sanitize(stmt.pp)});\n${next.pp}"
  }

  /** close rule */
  case class Close(app: SApp, selector: Expr, asn: Assertion, fresh_exist: SubstVar, next: ProofRule) extends  ProofRule {
    override def pp: String = s"${ind}Close(${app.pp}, ${sanitize(selector.pp)}, ${asn.pp}, {${fresh_exist.mkString(",")}});\n${next.pp}"
  }

  /** star partial */
  case class StarPartial(new_pre_phi: PFormula, new_post_phi: PFormula, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}StarPartial(${new_pre_phi.pp}, ${new_post_phi.pp});\n${next.pp}"
  }

  case class PickCard(map: Map[Var,Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}PickCard(${map.mkString(",")});\n${next.pp}"
  }


  case class PickArg(map: Map[Var, Expr], next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}PickArg(${map.mkString(",")});\n${next.pp}"
  }

  case class Init(goal: Goal, next: ProofRule) extends ProofRule {
    override def pp: String = s"${ind}Init(${goal.pp});\n${next.pp}"
  }

  case object Inconsistency extends ProofRule {
    override def pp: String = "Inconsistency"
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
        case IdProducer => node.children match {
          case ::(head, Nil) => ProofRule.CheckPost(of_certtree(head))
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