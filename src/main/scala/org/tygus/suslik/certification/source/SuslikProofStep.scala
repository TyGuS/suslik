package org.tygus.suslik.certification.source

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.traversal.Evaluator.DeferredsAction
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.certification.traversal.Step.SourceStep
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements.{Error, Guarded, Load, Skip, Solution, Store}
import org.tygus.suslik.language.{SSLType, Statements}
import org.tygus.suslik.logic.Preprocessor.findMatchingHeaplets
import org.tygus.suslik.logic.Specifications.{Assertion, Goal, GoalLabel, SuspendedCallGoal}
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.StmtProducerOps._
import org.tygus.suslik.synthesis.rules.LogicalRules.StarPartial.extendPure
import org.tygus.suslik.synthesis.rules._

import scala.annotation.tailrec
import scala.collection.immutable.Map

case class ProofRuleTranslationException(msg: String) extends Exception

/** compressed form of suslik rules */
sealed trait SuslikProofStep extends SourceStep {}

object SuslikProofStep {
  def sanitize (str: String) = str.replace(";\n","")

  /** corresponds to asserting all the variables in vars are not null */
  case class NilNotLval(vars: List[Expr]) extends SuslikProofStep {
    override def pp: String = s"NilNotLval(${vars.map(_.pp).mkString(", ")});"
  }

  /** solves a pure entailment with SMT */
  case class CheckPost(prePhi: PFormula, postPhi: PFormula, gamma: Gamma) extends SuslikProofStep {
    override def pp: String = s"CheckPost(${prePhi.pp}; ${postPhi.pp});"
  }

  /** picks an arbitrary instantiation of the proof rules */
  case class Pick(from: Var, to: Expr) extends SuslikProofStep {
    override def pp: String = s"Pick(${from.pp} -> ${to.pp});"
  }

  /** branches on a condition */
  case class Branch(cond: Expr) extends SuslikProofStep {
    override def pp: String = s"Branch(${cond.pp});"
  }

  /** the point at which a condition was abduced */
  case class AbduceBranch(cond: Expr) extends SuslikProofStep {
    override def pp: String = s"AbduceBranch(${cond.pp});"
  }

  /** write a value */
  case class Write(stmt: Store) extends SuslikProofStep {
    override def pp: String = s"Write(${sanitize(stmt.pp)});"
  }

  /** weaken the precondition by removing unused formulae */
  case class WeakenPre(unused: PFormula) extends SuslikProofStep {
    override def pp: String = s"WeakenPre(${unused.pp});"
  }

  /** empty rule */
  case class EmpRule(label: Option[GoalLabel]) extends SuslikProofStep {
    override def deferredsAction: DeferredsAction = DeferredsAction.PopLayer
    override def pp: String = s"EmpRule;"
  }

  /** pure synthesis rules */
  case class PureSynthesis(is_final: Boolean, assignments:Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"PureSynthesis(${is_final}, ${assignments.mkString(",")});"
  }

  /** open constructor cases */
  case class Open(pred: SApp, fresh_exists: SubstVar, fresh_params: Subst, selectors: List[Expr]) extends SuslikProofStep {
    override def pp: String = s"Open(${pred.pp}, existentials: ${fresh_exists.mkString(", ")}, params: ${fresh_params.mkString(", ")});"
  }

  /** subst L */
  case class SubstL(from: Var, to: Expr) extends SuslikProofStep {
    override def pp: String = s"SubstL(${from.pp} -> ${to.pp});"
  }

  /** subst R */
  case class SubstR(from: Var, to: Expr) extends SuslikProofStep {
    override def pp: String = s"SubstR(${from.pp} -> ${to.pp});"
  }


  /** read rule */
  case class Read(ghostFrom: Var, ghostTo: Var, operation: Load) extends SuslikProofStep {
    override def pp: String = s"Read(${ghostFrom.pp} -> ${ghostTo.pp}, ${sanitize(operation.pp)});"
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
  override def deferredsAction: DeferredsAction = DeferredsAction.PushLayer
  override def pp: String = {
    val new_vars_str = new_vars.map({case(Var(name), ty) => s"${name} -> ${ty.pp}"}).mkString(",")
    val fresh_sub_str = freshSub.map({case (Var(name), Var(to)) => s"${name} -> ${to}"}).mkString(",")
    val fresh_to_actual_sub = freshToActual.map({case (Var(name), expr) => s"${name} -> ${expr.pp}"}).mkString(",")
    s"AbduceCall(" +
      s"new_vars: {${new_vars_str}}, " +
      s"freshSub: {${fresh_sub_str}}," +
      s"freshToActual: {${fresh_to_actual_sub}}, " +
      s"pre: ${sanitize(f_pre.pp)}, " +
      s"post: ${sanitize(callePost.pp)}, " +
      s"call: ${sanitize(call.pp)}" +
      s");"
  }
}


  /** unification of heap (ignores block/pure distinction) */
  case class HeapUnify(subst: Map[Expr, Expr]) extends SuslikProofStep {
    override def pp: String = s"HeapUnify(${subst.mkString(",")});"
  }

  /** unification of pointers */
  case class HeapUnifyPointer(from: Var, to: Var) extends SuslikProofStep {
    override def pp: String = s"HeapUnifyPointer(${from.pp} -> ${to.pp});"
  }

  case class HeapUnifyUnfold(preApp: SApp, postApp: SApp, subst: Map[Expr, Expr]) extends SuslikProofStep {
    override def pp: String = s"HeapUnifyUnfold(${preApp.pp}, ${postApp.pp}, ${subst.mkString(",")})"
  }

  /** unfolds frame */
  case class FrameUnfold(h_pre: Heaplet, h_post: Heaplet) extends SuslikProofStep {
    override def pp: String = s"FrameUnfold(${h_pre.pp}, ${h_post.pp});"
  }

  /** call operation */
  case class Call(subst: Map[Var, Expr], call: Statements.Call) extends SuslikProofStep {
    override def deferredsAction: DeferredsAction = DeferredsAction.PopLayer
    override def pp: String = s"Call({${subst.mkString(",")}}, ${sanitize(call.pp)});"
  }

  /** free operation */
  case class Free(stmt: Statements.Free, size: Int) extends SuslikProofStep {
    override def pp: String = s"Free(${sanitize(stmt.pp)});"
  }

  /** malloc rule */
  case class Malloc(ghostFrom: Var, ghostTo: Var, stmt: Statements.Malloc) extends SuslikProofStep {
    override def pp: String = s"Malloc(${ghostFrom.pp} -> ${ghostTo.pp}, ${sanitize(stmt.pp)});"
  }

  /** close rule */
  case class Close(app: SApp, selector: Expr, asn: Assertion, fresh_exist: SubstVar) extends  SuslikProofStep {
    override def pp: String = s"Close(${app.pp}, ${sanitize(selector.pp)}, ${asn.pp}, {${fresh_exist.mkString(",")}});"
  }

  /** star partial */
  case class StarPartial(new_pre_phi: PFormula, new_post_phi: PFormula) extends SuslikProofStep {
    override def pp: String = s"StarPartial(${new_pre_phi.pp}, ${new_post_phi.pp});"
  }

  case class PickCard(from: Var, to: Expr) extends SuslikProofStep {
    override def pp: String = s"PickCard(${from.pp} -> ${to.pp});"
  }


  case class PickArg(from: Var, to: Var) extends SuslikProofStep {
    override def pp: String = s"PickArg(${from.pp} -> ${to.pp});"
  }

  case class Init(goal: Goal) extends SuslikProofStep {
    override def deferredsAction: DeferredsAction = DeferredsAction.PushLayer
    override def pp: String = s"Init(${goal.pp});"
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
      throw ProofRuleTranslationException(s"continuation for ${node.rule} is not what was expected: ${node.kont.toString}")
    def fail_with_bad_children(ls: Seq[CertTree.Node], count: Int): Nothing =
      throw ProofRuleTranslationException(s"unexpected number of children for proof rule ${node.rule} - ${ls.length} != $count")

    val label = Some(node.goal.label)
    node.rule match {
      case LogicalRules.NilNotLval => node.kont match {
        case IdProducer >> ExtractHelper(goal) =>
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
        case PureEntailmentProducer(prePhi, postPhi, gamma) >> IdProducer => node.children match {
          case ::(head, Nil) => SuslikProofStep.CheckPost(prePhi, postPhi, gamma)
          case ls => fail_with_bad_children(ls, 1)
        }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.Pick => node.kont match {
        case SubstProducer(from, to) >> IdProducer >> ExtractHelper(_) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.Pick(from, to)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case BranchRules.Branch => node.kont match {
        case GuardedBranchProducer(goal, unknown) =>
          node.children match {
            case ::(if_true, ::(if_false, Nil)) => SuslikProofStep.Branch(unknown)
            case ls => fail_with_bad_children(ls, 2)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case BranchRules.AbduceBranch => node.kont match {
        case GuardedProducer(cond) =>
          node.children match {
            case ::(if_true, Nil) => SuslikProofStep.AbduceBranch(cond)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.WriteRule => node.kont match {
        case PrependProducer(stmt@Store(_, _, _)) >> ExtractHelper(_) =>
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
        case IdProducer >> ExtractHelper(goal) =>
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
        case SubstMapProducer(assignments) >> IdProducer >> ExtractHelper(_) =>
          node.children match {
            case ::(head, Nil) =>
              SuslikProofStep.PureSynthesis(is_final = true, assignments)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.Open => node.kont match {
        case BranchProducer(Some(pred), fresh_vars, sbst, selectors) >> ExtractHelper(_) =>
          SuslikProofStep.Open(pred, fresh_vars, sbst, selectors.toList)
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.SubstLeft => node.kont match {
        case SubstProducer(from, to) >> IdProducer >> ExtractHelper(_) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.SubstL(from, to)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.SubstRight => node.kont match {
        case SubstProducer(from, to) >> IdProducer >> ExtractHelper(_) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.SubstR(from, to)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.ReadRule => node.kont match {
        case SubstVarProducer(from, to) >> PrependProducer(stmt@Load(_, _, _, _)) >> ExtractHelper(_) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.Read(from, to, stmt)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.AbduceCall => node.kont match {
        case AbduceCallProducer(f) >> IdProducer >> ExtractHelper(_) =>
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
        case UnificationProducer(_, _, subst) >> IdProducer >> ExtractHelper(_) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.HeapUnify(subst)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyUnfolding => node.kont match {
        case UnificationProducer(preApp:SApp, postApp: SApp, subst) >> IdProducer >> ExtractHelper(_) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.HeapUnifyUnfold(preApp, postApp, subst)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.HeapUnifyBlock => node.kont match {
        case UnificationProducer(_, _, subst) >> IdProducer >> ExtractHelper(_) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.HeapUnify(subst)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnificationRules.UnifyPointerFlat => node.kont match {
        case SubstVarProducer(from, to) >> IdProducer >> ExtractHelper(goal) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.HeapUnifyPointer(from, to)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case LogicalRules.FrameUnfolding => node.kont match {
        case IdProducer >> ExtractHelper(goal) =>
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
        case IdProducer >> ExtractHelper(goal) =>
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
        case IdProducer >> ExtractHelper(goal) =>
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
        case IdProducer >> ExtractHelper(goal) =>
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
        case SubstMapProducer(subst) >> PrependProducer(call: Statements.Call) >> ExtractHelper(_) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.Call(subst, call)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case OperationalRules.FreeRule => node.kont match {
        case PrependProducer(stmt@Statements.Free(Var(name))) >> ExtractHelper(_) =>
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
        case SubstVarProducer(from, to) >> PrependProducer(stmt@Statements.Malloc(_, _, _)) >> ExtractHelper(goal) =>
          node.children match {
            case ::(head, Nil) =>
              SuslikProofStep.
                Malloc(from, to, stmt)
            case ls => fail_with_bad_children(ls, 1)
          }
        case _ => fail_with_bad_proof_structure()
      }
      case UnfoldingRules.Close => node.kont match {
        case UnfoldProducer(app, selector, asn, fresh_exist) >> IdProducer >> ExtractHelper(_) =>
          node.children match {
            case ::(head, Nil) =>
              SuslikProofStep.Close(app, selector, asn, fresh_exist)
            case ls => fail_with_bad_children(ls, 1)
          }
      }
      case LogicalRules.StarPartial => node.kont match {
        case IdProducer >> ExtractHelper(goal) =>
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
        case SubstProducer(from, to) >> IdProducer >> ExtractHelper(goal) =>
          node.children match {
            case ::(head, Nil) => SuslikProofStep.PickCard(from, to)
            case ls => fail_with_bad_children(ls, 1)
          }
      }
      case UnificationRules.PickArg => node.kont match {
        case SubstVarProducer(from, to) >> IdProducer >> ExtractHelper(goal) =>
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
    case class Item(
                     step: SuslikProofStep,
                     label: Option[GoalLabel],
                     remaining: List[CertTree.Node],
                     doneTree: List[ProofTree[SuslikProofStep]],
                     doneProg: List[Solution],
                     kont: StmtProducer
                   )

    /**
      * Update parent with a child branch we've finished exploring
      * @param stack the continuation stack
      * @param result a translated child branch
      * @return a fully translated proof tree
      */
    @tailrec
    def backward(stack: List[Item], result: ProofTree[SuslikProofStep], prog: Solution): ProofTree[SuslikProofStep] = stack match {
      case Nil => result
      case currItem :: stack =>
        currItem.remaining match {
          case Nil =>
            // finished exploring all child branches of current node; go to parent
            val doneTree = (result :: currItem.doneTree).reverse
            val doneProg = (prog :: currItem.doneProg).reverse
            val finalProg = currItem.kont(doneProg)
            val finalTree = (currItem.step, currItem.kont) match {
              case (Branch(_), GuardedBranchProducer(goal, _)) =>
                doneProg.headOption match {
                  case Some((Guarded(cond, _), _)) if BranchRules.Branch.isBranchingPoint(goal, cond) =>
                    // Current goal is the branching point: create branch step with finalized conditional
                    ProofTree(Branch(cond), doneTree, currItem.label)
                  case _ =>
                    // Current goal is not the branching point: second child is always vacuous, so ignore it
                    doneTree.head
                }
              case _ => ProofTree(currItem.step, doneTree, currItem.label)
            }
            backward(stack, finalTree, finalProg)
          case nextChild :: remaining =>
            // current node still has unexplored child branches; explore the next one
            val updatedCurr = currItem.copy(remaining = remaining, doneTree = result :: currItem.doneTree, doneProg = prog :: currItem.doneProg)
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
        case Nil => backward(stack, ProofTree(step, Nil, label), tree.kont(Nil))
        case next :: remaining =>
          val item = Item(step, label, remaining, Nil, Nil, tree.kont)
          val nextStack = item :: stack
          forward(next, nextStack)
      }
    }

    val initStep = Init(node.goal)
    val initItem = Item(initStep, None, Nil, Nil, Nil, IdProducer)
    val res = forward(node, List(initItem))
//    Console.println(SuslikPrinter.pp(res))
    res
  }
}