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
sealed trait SuslikProofStep extends PrettyPrinting {
}

object SuslikProofStep {

  implicit object ProofTreePrinter extends ProofTreePrinter[SuslikProofStep] {
    override def pp(tree: ProofTree[SuslikProofStep]): String =
      tree.rule match {
        case rule@AbduceBranch(cond) =>
          rule.pp ++ "\n" ++ rule.branch_strings(tree.children(0), tree.children(1))
        case rule@Open(_, _, _, _) => rule.pp ++ "\n" ++ rule.branch_strings(tree.children)
        case rule => rule.pp ++ "\n" ++ tree.children.map(_.pp).mkString("\n")
      }
  }



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
  case class NilNotLval(vars: List[Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}NilNotLval(${vars.map(_.pp).mkString(", ")});"
  }

  /** solves a pure entailment with SMT */
  case class CheckPost(prePhi: PFormula, postPhi: PFormula) extends SuslikProofStep {
    override def pp: String = s"${ind}CheckPost(${prePhi.pp}; ${postPhi.pp});"
  }

  /** picks an arbitrary instantiation of the proof rules */
  case class Pick(subst: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}Pick(${subst.mkString(", ")});"
  }

  /** abduces a condition for the proof */
  case class AbduceBranch(cond: Expr) extends SuslikProofStep {
    def branch_strings[T <: PrettyPrinting] (ifTrue: T, ifFalse: T) =
    s"${ind}IfTrue:\\n${with_scope(_ => ifTrue.pp)}\\n${ind}IfFalse:\\n${with_scope(_ => ifFalse.pp)}"

    override def pp: String = s"${ind}AbduceBranch(${cond});"
  }

  /** write a value */
  case class Write(stmt: Store) extends SuslikProofStep {
    override def pp: String = s"${ind}Write(${sanitize(stmt.pp)});"
  }

  /** weaken the precondition by removing unused formulae */
  case class WeakenPre(unused: PFormula) extends SuslikProofStep {
    override def pp: String = s"${ind}WeakenPre(${unused.pp});"
  }

  /** empty rule */
  case object EmpRule extends SuslikProofStep {
    override def pp: String = s"${ind}EmpRule;"
  }

  /** pure synthesis rules */
  case class PureSynthesis(is_final: Boolean, assignments:Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}PureSynthesis(${is_final}, ${assignments.mkString(",")});"
  }

  /** open constructor cases */
  case class Open(pred: SApp, fresh_vars: SubstVar, sbst: Subst, cases: List[Expr]) extends SuslikProofStep {
    def branch_strings[T <: PrettyPrinting] (exprs: List[T]) =
      s"${with_scope(_ => exprs.zip(cases).map({case (expr,rest) => s"${ind}if ${sanitize(expr.pp)}:\n${with_scope(_ => rest.pp)}"}).mkString("\n"))}"
    override def pp: String = s"${ind}Open(${pred.pp}, ${fresh_vars.mkString(", ")});"
  }

  /** subst L */
  case class SubstL(map: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}SubstL(${map.mkString(",")});"
  }

  /** subst R */
  case class SubstR(map: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}SubstR(${map.mkString(",")});"
  }


  /** read rule */
  case class Read(map: Map[Var,Var], operation: Load) extends SuslikProofStep {
    override def pp: String = s"${ind}Read(${map.mkString(",")}, ${sanitize(operation.pp)});"
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
                       gamma: Gamma
                     ) extends SuslikProofStep {
  override def pp: String = s"${ind}AbduceCall({${new_vars.mkString(",")}}, ${sanitize(f_pre.pp)}, ${sanitize(callePost.pp)}, ${sanitize(call.pp)}, {${freshSub.mkString(",")}});"
}


  /** unification of heap (ignores block/pure distinction) */
  case class HeapUnify(subst: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}HeapUnify(${subst.mkString(",")});"
  }

  /** unification of pointers */
  case class HeapUnifyPointer(map: Map[Var,Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}HeapUnifyPointer(${map.mkString(",")});"
  }

  /** unfolds frame */
  case class FrameUnfold(h_pre: Heaplet, h_post: Heaplet) extends SuslikProofStep {
    override def pp: String = s"${ind}FrameUnfold(${h_pre.pp}, ${h_post.pp});"
  }

  /** call operation */
  case class Call(subst: Map[Var, Expr], call: Statements.Call) extends SuslikProofStep {
    override def pp: String = s"${ind}Call({${subst.mkString(",")}}, ${sanitize(call.pp)});"
  }

  /** free operation */
  case class Free(stmt: Statements.Free, size: Int) extends SuslikProofStep {
    override def pp: String = s"${ind}Free(${sanitize(stmt.pp)});"
  }

  /** malloc rule */
  case class Malloc(map: SubstVar, stmt: Statements.Malloc) extends SuslikProofStep {
    override def pp: String = s"${ind}Malloc(${map.mkString(",")}, ${sanitize(stmt.pp)});"
  }

  /** close rule */
  case class Close(app: SApp, selector: Expr, asn: Assertion, fresh_exist: SubstVar) extends  SuslikProofStep {
    override def pp: String = s"${ind}Close(${app.pp}, ${sanitize(selector.pp)}, ${asn.pp}, {${fresh_exist.mkString(",")}});"
  }

  /** star partial */
  case class StarPartial(new_pre_phi: PFormula, new_post_phi: PFormula) extends SuslikProofStep {
    override def pp: String = s"${ind}StarPartial(${new_pre_phi.pp}, ${new_post_phi.pp});"
  }

  case class PickCard(map: Map[Var,Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}PickCard(${map.mkString(",")});"
  }


  case class PickArg(map: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}PickArg(${map.mkString(",")});"
  }

  case class Init(goal: Goal) extends SuslikProofStep {
    override def pp: String = s"${ind}Init(${goal.pp});"
  }

  case object Inconsistency extends SuslikProofStep {
    override def pp: String = "Inconsistency;"
  }


  /** converts a Suslik CertTree node into the unified ProofRule structure */
  def of_certtree(node: CertTree.Node): ProofTree[SuslikProofStep] = {
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
            case ::(head, Nil) => ProofTree(SuslikProofStep.NilNotLval(pre_pointers), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case FailRules.CheckPost => node.kont match {
        case ChainedProducer(PureEntailmentProducer(prePhi, postPhi), IdProducer) => node.children match {
          case ::(head, Nil) => ProofTree(SuslikProofStep.CheckPost(prePhi, postPhi), List(of_certtree(head)))
          case ls => fail_with_bad_children(ls, 1)
        }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.Pick => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.Pick(map), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case FailRules.AbduceBranch => node.kont match {
        case GuardedProducer(cond, _) =>
          node.children match {
            case ::(if_true, ::(if_false, Nil)) => ProofTree(SuslikProofStep.AbduceBranch(cond), List(of_certtree(if_true), of_certtree(if_false)))
            case ls => fail_with_bad_children(ls, 2)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.WriteRule => node.kont match {
        case ChainedProducer(ChainedProducer(PrependProducer(stmt@Store(_, _, _)), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.Write(stmt), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.Inconsistency => node.kont match {
        case ConstProducer(Error) =>
          node.children match {
            case Nil => ProofTree(SuslikProofStep.Inconsistency, List())
            case ls => fail_with_bad_children(ls, 0)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.WeakenPre => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          val unused = goal.pre.phi.indepedentOf(goal.pre.sigma.vars ++ goal.post.vars)
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.WeakenPre(unused), List(of_certtree(head)))

            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.EmpRule => node.kont match {
        case ConstProducer(Skip) =>
          node.children match {
            case Nil => ProofTree(SuslikProofStep.EmpRule, List())
            case ls => fail_with_bad_children(ls, 0)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case DelegatePureSynthesis.PureSynthesisFinal => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(assignments), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) =>
              ProofTree(SuslikProofStep.PureSynthesis(is_final = true, assignments), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.Open => node.kont match {
        case ChainedProducer(ChainedProducer(BranchProducer(Some(pred), fresh_vars, sbst, selectors), HandleGuard(_)), ExtractHelper(_)) =>
          ProofTree(SuslikProofStep.Open(pred, fresh_vars, sbst, selectors.toList), node.children.map(of_certtree).toList)
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.SubstLeft => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.SubstL(map), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.SubstRight => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.SubstR(map), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.ReadRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(GhostSubstProducer(map), PrependProducer(stmt@Load(_, _, _, _))), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.Read(map, stmt), List(of_certtree(head)))
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
              ProofTree(SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, head.goal.gamma), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyPure => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.HeapUnify(subst), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyUnfolding => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.HeapUnify(subst), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyBlock => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.HeapUnify(subst), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyPointer => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.HeapUnifyPointer(subst), List(of_certtree(head)))
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
                  ProofTree(SuslikProofStep.FrameUnfold(h_pre, h_post), List(of_certtree(head)))
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
                  ProofTree(SuslikProofStep.FrameUnfold(h_pre, h_post), List(of_certtree(head)))
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
                  ProofTree(SuslikProofStep.FrameUnfold(h_pre, h_post), List(of_certtree(head)))
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
                  ProofTree(SuslikProofStep.FrameUnfold(h_pre, h_post), List(of_certtree(head)))
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.CallRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst),PrependProducer(call: Statements.Call)), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.Call(subst, call), List(of_certtree(head)))
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
            case ::(head, Nil) => ProofTree(SuslikProofStep.Free(stmt, size), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.AllocRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(GhostSubstProducer(map), PrependProducer(stmt@Statements.Malloc(_, _, _))), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
                ProofTree(Malloc(map, stmt), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.Close => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(UnfoldProducer(app, selector, asn, fresh_exist), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) =>
              ProofTree(SuslikProofStep.Close(app, selector, asn, fresh_exist), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
      }
      case LogicalRules.StarPartial => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          val new_pre_phi = extendPure(goal.pre.phi, goal.pre.sigma)
          val new_post_phi = extendPure(goal.pre.phi && goal.post.phi, goal.post.sigma)

          node.children match {
            case ::(head, Nil) =>
              ProofTree(SuslikProofStep.StarPartial(new_pre_phi, new_post_phi), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }

      case UnificationRules.PickCard => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.PickCard(map), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
      }
      case UnificationRules.PickArg => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => ProofTree(SuslikProofStep.PickArg(map), List(of_certtree(head)))
            case ls => fail_with_bad_children(ls, 1)
          }
      }
    }
  }
}