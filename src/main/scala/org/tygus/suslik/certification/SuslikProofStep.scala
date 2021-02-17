package org.tygus.suslik.certification

import org.tygus.suslik.certification.targets.vst.translation.Translation.TranslationException
import org.tygus.suslik.certification.traversal.Evaluator.EnvAction
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter}
import org.tygus.suslik.certification.traversal.Step.SourceStep
import org.tygus.suslik.language.Expressions.{Expr, NilPtr, Subst, SubstVar, Var}
import org.tygus.suslik.language.Statements.{Error, Load, Skip, Store}
import org.tygus.suslik.language.{PrettyPrinting, SSLType, Statements}
import org.tygus.suslik.logic.Preprocessor.findMatchingHeaplets
import org.tygus.suslik.logic.Specifications.{Assertion, Goal, GoalLabel, SuspendedCallGoal}
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis.rules.LogicalRules.StarPartial.extendPure
import org.tygus.suslik.synthesis.rules._
import org.tygus.suslik.synthesis.StmtProducer._

import scala.annotation.tailrec
import scala.collection.immutable.Map


/** compressed form of suslik rules */
trait SuslikProofStep extends SourceStep {}

object SuslikProofStep {
  implicit object ProofTreePrinter extends ProofTreePrinter[SuslikProofStep] {
    override def pp(tree: ProofTree[SuslikProofStep]): String =
      tree.step match {
        case rule:Branch => rule.pp ++ "\n" ++ rule.branch_strings(tree.children.head, tree.children(1))
        case rule:Open => rule.pp ++ "\n" ++ rule.branch_strings(tree.children)
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
  case class Pick(from: Var, to: Expr) extends SuslikProofStep {
    override def pp: String = s"${ind}Pick(${from.pp} -> ${to.pp});"
  }

  /** branches on a condition */
  case class Branch(cond: Expr, bLabel: GoalLabel) extends SuslikProofStep {
    def branch_strings[T <: PrettyPrinting] (ifTrue: T, ifFalse: T) =
      s"${ind}IfTrue:\n${with_scope(_ => ifTrue.pp)}\n${ind}IfFalse:\n${with_scope(_ => ifFalse.pp)}"

    override def pp: String = s"${ind}AbduceBranch(${cond.pp}, ${bLabel.pp});"
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
  case class EmpRule(label: Option[GoalLabel]) extends SuslikProofStep {
    override def contextAction: EnvAction = EnvAction.PopLayer
    override def pp: String = s"${ind}EmpRule;"
  }

  /** pure synthesis rules */
  case class PureSynthesis(is_final: Boolean, assignments:Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}PureSynthesis(${is_final}, ${assignments.mkString(",")});"
  }

  /** open constructor cases */
  case class Open(pred: SApp, fresh_vars: SubstVar, sbst: Subst, selectors: List[Expr]) extends SuslikProofStep {
    def branch_strings[T <: PrettyPrinting] (exprs: List[T]) =
      s"${with_scope(_ => selectors.zip(exprs).map({case (sel,rest) => s"${ind}if ${sanitize(sel.pp)}:\n${with_scope(_ => rest.pp)}"}).mkString("\n"))}"

    override def pp: String = s"${ind}Open(${pred.pp}, ${fresh_vars.mkString(", ")});"
  }

  /** subst L */
  case class SubstL(from: Var, to: Expr) extends SuslikProofStep {
    override def pp: String = s"${ind}SubstL(${from.pp} -> ${to.pp});"
  }

  /** subst R */
  case class SubstR(from: Var, to: Expr) extends SuslikProofStep {
    override def pp: String = s"${ind}SubstR(${from.pp} -> ${to.pp});"
  }


  /** read rule */
  case class Read(ghostFrom: Var, ghostTo: Var, operation: Load) extends SuslikProofStep {
    override def pp: String = s"${ind}Read(${ghostFrom.pp} -> ${ghostTo.pp}, ${sanitize(operation.pp)});"
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
    override def contextAction: EnvAction = EnvAction.PushLayer
    override def pp: String = s"${ind}AbduceCall({${new_vars.mkString(",")}}, ${sanitize(f_pre.pp)}, ${sanitize(callePost.pp)}, ${sanitize(call.pp)}, {${freshSub.mkString(",")}});"
  }


  /** unification of heap (ignores block/pure distinction) */
  case class HeapUnify(subst: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"${ind}HeapUnify(${subst.mkString(",")});"
  }

  /** unification of pointers */
  case class HeapUnifyPointer(from: Var, to: Var) extends SuslikProofStep {
    override def pp: String = s"${ind}HeapUnifyPointer(${from.pp} -> ${to.pp});"
  }

  /** unfolds frame */
  case class FrameUnfold(h_pre: Heaplet, h_post: Heaplet) extends SuslikProofStep {
    override def pp: String = s"${ind}FrameUnfold(${h_pre.pp}, ${h_post.pp});"
  }

  /** call operation */
  case class Call(subst: Map[Var, Expr], call: Statements.Call) extends SuslikProofStep {
    override def contextAction: EnvAction = EnvAction.PopLayer
    override def pp: String = s"${ind}Call({${subst.mkString(",")}}, ${sanitize(call.pp)});"
  }

  /** free operation */
  case class Free(stmt: Statements.Free, size: Int) extends SuslikProofStep {
    override def pp: String = s"${ind}Free(${sanitize(stmt.pp)});"
  }

  /** malloc rule */
  case class Malloc(ghostFrom: Var, ghostTo: Var, stmt: Statements.Malloc) extends SuslikProofStep {
    override def pp: String = s"${ind}Malloc(${ghostFrom.pp} -> ${ghostTo.pp}, ${sanitize(stmt.pp)});"
  }

  /** close rule */
  case class Close(app: SApp, selector: Expr, asn: Assertion, fresh_exist: SubstVar) extends  SuslikProofStep {
    override def pp: String = s"${ind}Close(${app.pp}, ${sanitize(selector.pp)}, ${asn.pp}, {${fresh_exist.mkString(",")}});"
  }

  /** star partial */
  case class StarPartial(new_pre_phi: PFormula, new_post_phi: PFormula) extends SuslikProofStep {
    override def pp: String = s"${ind}StarPartial(${new_pre_phi.pp}, ${new_post_phi.pp});"
  }

  case class PickCard(from: Var, to: Expr) extends SuslikProofStep {
    override def pp: String = s"${ind}PickCard(${from.pp} -> ${to.pp});"
  }


  case class PickArg(from: Var, to: Var) extends SuslikProofStep {
    override def pp: String = s"${ind}PickArg(${from.pp} -> ${to.pp});"
  }

  case class Init(goal: Goal) extends SuslikProofStep {
    override def contextAction: EnvAction = EnvAction.PushLayer
    override def pp: String = s"${ind}Init(${goal.pp});"
  }

  case class Inconsistency(label: Option[GoalLabel]) extends SuslikProofStep {
    override def pp: String = "Inconsistency"
  }

  /**
    * Use CertTree node info to generate a SuslikProofStep corresponding to the node's SynthesisRule
    * @param node a Suslik CertTree node
    * @return a SuslikProofStep
    */
  def translate(node: CertTree.Node): SuslikProofStep = {
    def fail_with_bad_proof_structure(): Nothing =
      throw TranslationException(s"continuation for ${node.rule} is not what was expected: ${node.kont.toString}")
    def fail_with_bad_children(ls: Seq[CertTree.Node], count: Int): Nothing =
      throw TranslationException(s"unexpected number of children for proof rule ${node.rule} - ${ls.length} != $count")

    val label = Some(node.goal.label)
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
            case ::(head, Nil) => SuslikProofStep.NilNotLval(pre_pointers)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case FailRules.CheckPost => node.kont match {
        case ChainedProducer(PureEntailmentProducer(prePhi, postPhi), IdProducer) => node.children match {
          case ::(head, Nil) => SuslikProofStep.CheckPost(prePhi, postPhi)
          case ls => fail_with_bad_children(ls, 1)
        }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.Pick => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(from, to), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.Pick(from, to)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case FailRules.AbduceBranch => node.kont match {
        case GuardedProducer(cond, bGoal) =>
          node.children match {
            case ::(if_true, ::(if_false, Nil)) => SuslikProofStep.Branch(cond, bGoal.label)
            case ls => fail_with_bad_children(ls, 2)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.WriteRule => node.kont match {
        case ChainedProducer(ChainedProducer(PrependProducer(stmt@Store(_, _, _)), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.Write(stmt)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.Inconsistency => node.kont match {
        case ConstProducer(Error) =>
          node.children match {
            case Nil => SuslikProofStep.Inconsistency(label)
            case ls => fail_with_bad_children(ls, 0)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.WeakenPre => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          val unused = goal.pre.phi.indepedentOf(goal.pre.sigma.vars ++ goal.post.vars)
          node.children match {
            case ::(head, Nil) => SuslikProofStep.WeakenPre(unused)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.EmpRule => node.kont match {
        case ConstProducer(Skip) =>
          node.children match {
            case Nil => SuslikProofStep.EmpRule(label)
            case ls => fail_with_bad_children(ls, 0)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case DelegatePureSynthesis.PureSynthesisFinal => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstMapProducer(assignments), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) =>
              SuslikProofStep.PureSynthesis(is_final = true, assignments)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.Open => node.kont match {
        case ChainedProducer(ChainedProducer(BranchProducer(Some(pred), fresh_vars, sbst, selectors), HandleGuard(_)), ExtractHelper(_)) =>
          SuslikProofStep.Open(pred, fresh_vars, sbst, selectors.toList)
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.SubstLeft => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(from, to), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.SubstL(from, to)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.SubstRight => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(from, to), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.SubstR(from, to)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.ReadRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstVarProducer(from, to), PrependProducer(stmt@Load(_, _, _, _))), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.Read(from, to, stmt)
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
              SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, freshSub, freshToActual, f, head.goal.gamma)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyPure => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstMapProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.HeapUnify(subst)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyUnfolding => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstMapProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.HeapUnify(subst)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyBlock => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstMapProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.HeapUnify(subst)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyPointer => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstVarProducer(from, to), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.HeapUnifyPointer(from, to)
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
                  SuslikProofStep.FrameUnfold(h_pre, h_post)
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
                  SuslikProofStep.FrameUnfold(h_pre, h_post)
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
                  SuslikProofStep.FrameUnfold(h_pre, h_post)
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
                  SuslikProofStep.FrameUnfold(h_pre, h_post)
              }
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.CallRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstMapProducer(subst),PrependProducer(call: Statements.Call)), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.Call(subst, call)
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
            case ::(head, Nil) => SuslikProofStep.Free(stmt, size)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.AllocRule => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstVarProducer(from, to), PrependProducer(stmt@Statements.Malloc(_, _, _))), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) =>
              SuslikProofStep.
                Malloc(from, to, stmt)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.Close => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(UnfoldProducer(app, selector, asn, fresh_exist), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
          node.children match {
            case ::(head, Nil) =>
              SuslikProofStep.Close(app, selector, asn, fresh_exist)
            case ls => fail_with_bad_children(ls, 1)
          }
      }
      case LogicalRules.StarPartial => node.kont match {
        case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
          val new_pre_phi = extendPure(goal.pre.phi, goal.pre.sigma)
          val new_post_phi = extendPure(goal.pre.phi && goal.post.phi, goal.post.sigma)

          node.children match {
            case ::(head, Nil) =>
              SuslikProofStep.StarPartial(new_pre_phi, new_post_phi)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }

      case UnificationRules.PickCard => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(from, to), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.PickCard(from, to)
            case ls => fail_with_bad_children(ls, 1)
          }
      }
      case UnificationRules.PickArg => node.kont match {
        case ChainedProducer(ChainedProducer(ChainedProducer(SubstVarProducer(from, to), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.PickArg(from, to)
            case ls => fail_with_bad_children(ls, 1)
          }
      }
    }
  }

  /**
    * Convert a Suslik CertTree node into the unified ProofTree structure
    * @param node a Suslik CertTree node
    * @return a corresponding ProofTree
    */
  def of_certtree(node: CertTree.Node): ProofTree[SuslikProofStep] = {
    case class Item(step: SuslikProofStep, label: Option[GoalLabel], remaining: List[CertTree.Node], done: List[ProofTree[SuslikProofStep]])

    /**
      * Update parent with a child branch we've finished exploring
      * @param stack the continuation stack
      * @param result a translated child branch
      * @return a fully translated proof tree
      */
    @tailrec
    def backward(stack: List[Item], result: ProofTree[SuslikProofStep]): ProofTree[SuslikProofStep] = stack match {
      case Nil => result
      case currItem :: stack =>
        currItem.remaining match {
          case Nil =>
            // finished exploring all child branches of current node; go to parent
            val done = result :: currItem.done
            backward(stack, ProofTree(currItem.step, done.reverse, currItem.label))
          case nextChild :: remaining =>
            // current node still has unexplored child branches; explore the next one
            val updatedCurr = currItem.copy(remaining = remaining, done = result :: currItem.done)
            forward(nextChild, updatedCurr :: stack)
        }
    }

    /**
      * Do step-wise translation of current CertTree node, handle any branch abductions, and explore children
      * @param tree the current CertTree node being explored
      * @param stack the continuation stack
      * @return a fully translated proof tree
      */
    @tailrec
    def forward(tree: CertTree.Node, stack: List[Item]): ProofTree[SuslikProofStep] = {
      val step = translate(tree)
      val label = Some(tree.goal.label)
      tree.children match {
        case Nil => backward(stack, ProofTree(step, Nil, label))
        case next :: remaining =>
          val item = Item(step, label, remaining, Nil)
          val nextStack = step match {
            // branch statement abduced to the current position; push on top of stack
            case ab: Branch if label.contains(ab.bLabel) => item :: stack
            // branch statement abduced to an ancestor; find and insert at correct position
            case ab: Branch => insertBranchPoint(item, ab.bLabel, stack, identity)
            // non-branch statement; push on top of stack
            case _ => item :: stack
          }
          forward(next, nextStack)
      }
    }

    /**
      * Look through tree traversal continuation stack to insert correct branching point for a branch abduction step.
      *
      * Consider in the left diagram, an AbduceBranch node B with children C (true case) and D (false case), and
      * intended branch destination A. This procedure modifies the traversal continuation so that B is the direct
      * parent of A.
      *
      *
      *           D---            D---
      *          /       =>      /
      * --A-----B-C---        --B-A-----C---
      *
      * @param item the branch abduction step
      * @param label the target goal label
      * @param stack the tree traversal continuation stack
      * @param k this function's own continuation for traversing the stack (note: different from tree traversal continuation)
      * @return the modified traversal continuation stack w/ finalized branch location
      */
    @tailrec
    def insertBranchPoint(item: Item, label: GoalLabel, stack: List[Item], k: List[Item] => List[Item]): List[Item] =
      stack match {
        case next :: rest =>
          next.step match {
            // found target goal label ('A' in the diagram); insert branch point immediately before it
            case _ if next.label.contains(label) => k(next :: item :: rest)
            // found a previous branch abduction with matching target goal label (happens if two branch abductions use the same branching point)
            case abduceBranch: Branch if abduceBranch.bLabel == label => k(item :: next :: rest)
            // didn't find target goal label; check parent
            case _ => insertBranchPoint(item, label, rest, ret => k(next :: ret))
          }
        case Nil => throw TranslationException(s"branch point ${label.pp} not found for branch abduction step ${item.step.pp}")
      }

    val initStep = Init(node.goal)
    val initItem = Item(initStep, None, Nil, Nil)
    val res = forward(node, List(initItem))
    Console.println(res.pp)
    res
  }
}
