package org.tygus.suslik.certification

import org.tygus.suslik.certification.targets.vst.translation.ProofTranslation.ProofRuleTranslationException
import org.tygus.suslik.language.Expressions.{Expr, NilPtr, Subst, SubstVar, Var}
import org.tygus.suslik.language.Statements.{Error, Load, Skip, Store}
import org.tygus.suslik.language.{PrettyPrinting, SSLType, Statements}
import org.tygus.suslik.logic.Preprocessor.{findMatchingHeaplets, sameLhs}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal, GoalLabel, SuspendedCallGoal}
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis.rules.LogicalRules.StarPartial.extendPure
import org.tygus.suslik.synthesis.rules._
import org.tygus.suslik.synthesis._

import scala.collection.immutable.Map



/** compressed form of suslik rules */
sealed abstract class SuslikProofStep extends PrettyPrinting {
  val label: Option[GoalLabel]
}

object SuslikProofStep {
  implicit object ProofTreePrinter extends ProofTreePrinter[SuslikProofStep] {
    override def pp(tree: ProofTree[SuslikProofStep]): String =
      tree.rule match {
        case rule:AbduceBranch =>
          rule.pp ++ "\n" ++ rule.branch_strings(tree.children.head, tree.children(1))
        case rule:Branch =>
          rule.pp ++ "\n" ++ rule.branch_strings(tree.children.head, tree.children(1))
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
  case class NilNotLval(label: Option[GoalLabel], vars: List[Expr]) extends SuslikProofStep {
    override def pp: String = s"NilNotLval(${vars.map(_.pp).mkString(", ")});"
  }

  /** solves a pure entailment with SMT */
  case class CheckPost(label: Option[GoalLabel], prePhi: PFormula, postPhi: PFormula) extends SuslikProofStep {
    override def pp: String = s"CheckPost(${prePhi.pp}; ${postPhi.pp});"
  }

  /** picks an arbitrary instantiation of the proof rules */
  case class Pick(label: Option[GoalLabel], subst: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"Pick(${subst.mkString(", ")});"
  }

  /** abduces a condition for the proof */
  case class AbduceBranch(label: Option[GoalLabel], cond: Expr, bLabel: GoalLabel) extends SuslikProofStep {
    def branch_strings[T <: PrettyPrinting] (ifTrue: T, ifFalse: T) =
      s"${ind}IfTrue:\\n${with_scope(_ => ifTrue.pp)}\\n${ind}IfFalse:\\n${with_scope(_ => ifFalse.pp)}"

    override def pp: String = s"AbduceBranch(${cond.pp}, ${bLabel.pp});"
  }

  /** write a value */
  case class Write(label: Option[GoalLabel], stmt: Store) extends SuslikProofStep {
    override def pp: String = s"Write(${sanitize(stmt.pp)});"
  }

  /** weaken the precondition by removing unused formulae */
  case class WeakenPre(label: Option[GoalLabel], unused: PFormula) extends SuslikProofStep {
    override def pp: String = s"WeakenPre(${unused.pp});"
  }

  /** empty rule */
  case class EmpRule(label: Option[GoalLabel]) extends SuslikProofStep {
    override def pp: String = s"EmpRule;"
  }

  /** pure synthesis rules */
  case class PureSynthesis(label: Option[GoalLabel], is_final: Boolean, assignments:Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"PureSynthesis(${is_final}, ${assignments.mkString(",")});"
  }

  /** open constructor cases */
  case class Open(label: Option[GoalLabel], pred: SApp, fresh_vars: SubstVar, sbst: Subst, selectors: List[Expr]) extends SuslikProofStep {
    def branch_strings[T <: PrettyPrinting] (exprs: List[T]) =
      s"${with_scope(_ => exprs.zip(selectors).map({case (expr,rest) => s"${ind}if ${sanitize(expr.pp)}:\n${with_scope(_ => rest.pp)}"}).mkString("\n"))}"

    override def pp: String = s"Open(${pred.pp}, ${fresh_vars.mkString(", ")});"
  }

  /** subst L */
  case class SubstL(label: Option[GoalLabel], map: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"SubstL(${map.mkString(",")});"
  }

  /** subst R */
  case class SubstR(label: Option[GoalLabel], map: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"SubstR(${map.mkString(",")});"
  }


  /** read rule */
  case class Read(label: Option[GoalLabel], map: Map[Var,Var], operation: Load) extends SuslikProofStep {
    override def pp: String = s"Read(${map.mkString(",")}, ${sanitize(operation.pp)});"
  }

//  /** abduce a call */
case class AbduceCall(
                       label: Option[GoalLabel],
                       new_vars: Map[Var, SSLType],
                       f_pre: Specifications.Assertion,
                       callePost: Specifications.Assertion,
                       call: Statements.Call,
                       freshSub: SubstVar,
                       freshToActual: Subst,
                       f: FunSpec,
                       gamma: Gamma
                     ) extends SuslikProofStep {
  override def pp: String = s"AbduceCall({${new_vars.mkString(",")}}, ${sanitize(f_pre.pp)}, ${sanitize(callePost.pp)}, ${sanitize(call.pp)}, {${freshSub.mkString(",")}});"
}


  /** unification of heap (ignores block/pure distinction) */
  case class HeapUnify(label: Option[GoalLabel], subst: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"HeapUnify(${subst.mkString(",")});"
  }

  /** unification of pointers */
  case class HeapUnifyPointer(label: Option[GoalLabel], map: Map[Var,Expr]) extends SuslikProofStep {
    override def pp: String = s"HeapUnifyPointer(${map.mkString(",")});"
  }

  /** unfolds frame */
  case class FrameUnfold(label: Option[GoalLabel], h_pre: Heaplet, h_post: Heaplet) extends SuslikProofStep {
    override def pp: String = s"FrameUnfold(${h_pre.pp}, ${h_post.pp});"
  }

  /** call operation */
  case class Call(label: Option[GoalLabel], subst: Map[Var, Expr], call: Statements.Call) extends SuslikProofStep {
    override def pp: String = s"Call({${subst.mkString(",")}}, ${sanitize(call.pp)});"
  }

  /** free operation */
  case class Free(label: Option[GoalLabel], stmt: Statements.Free, size: Int) extends SuslikProofStep {
    override def pp: String = s"Free(${sanitize(stmt.pp)});"
  }

  /** malloc rule */
  case class Malloc(label: Option[GoalLabel], map: SubstVar, stmt: Statements.Malloc) extends SuslikProofStep {
    override def pp: String = s"Malloc(${map.mkString(",")}, ${sanitize(stmt.pp)});"
  }

  /** close rule */
  case class Close(label: Option[GoalLabel], app: SApp, selector: Expr, asn: Assertion, fresh_exist: SubstVar) extends  SuslikProofStep {
    override def pp: String = s"Close(${app.pp}, ${sanitize(selector.pp)}, ${asn.pp}, {${fresh_exist.mkString(",")}});"
  }

  /** star partial */
  case class StarPartial(label: Option[GoalLabel], new_pre_phi: PFormula, new_post_phi: PFormula) extends SuslikProofStep {
    override def pp: String = s"StarPartial(${new_pre_phi.pp}, ${new_post_phi.pp});"
  }

  case class PickCard(label: Option[GoalLabel], map: Map[Var,Expr]) extends SuslikProofStep {
    override def pp: String = s"PickCard(${map.mkString(",")});"
  }


  case class PickArg(label: Option[GoalLabel], map: Map[Var, Expr]) extends SuslikProofStep {
    override def pp: String = s"PickArg(${map.mkString(",")});"
  }

  case class Init(label: Option[GoalLabel], goal: Goal) extends SuslikProofStep {
    override def pp: String = s"Init(${goal.pp});"
  }

  case class Inconsistency(label: Option[GoalLabel]) extends SuslikProofStep {
    override def pp: String = "Inconsistency"
  }

  case class Branch(label: Option[GoalLabel], cond: Expr) extends SuslikProofStep {
    def branch_strings[T <: PrettyPrinting] (ifTrue: T, ifFalse: T) =
      s"${ind}IfTrue:\\n${with_scope(_ => ifTrue.pp)}\\n${ind}IfFalse:\\n${with_scope(_ => ifFalse.pp)}"

    override def pp: String = s"Branch(${cond.pp});"
  }

  /** converts a Suslik CertTree node into the unified ProofRule structure */
  def of_certtree(node: CertTree.Node): ProofTree[SuslikProofStep] = {
    def fail_with_bad_proof_structure(): Nothing =
      throw ProofRuleTranslationException(s"continuation for ${node.rule} is not what was expected: ${node.kont.toString}")
    def fail_with_bad_children(ls: Seq[CertTree.Node], count: Int): Nothing =
      throw ProofRuleTranslationException(s"unexpected number of children for proof rule ${node.rule} - ${ls.length} != $count")

    def visit(node: CertTree.Node): ProofTree[SuslikProofStep] = {
      val label = Some(node.goal.label)
      val rule = node.rule match {
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
              case ::(head, Nil) => SuslikProofStep.NilNotLval(label, pre_pointers)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case FailRules.CheckPost => node.kont match {
          case ChainedProducer(PureEntailmentProducer(prePhi, postPhi), IdProducer) => node.children match {
            case ::(head, Nil) => SuslikProofStep.CheckPost(label, prePhi, postPhi)
            case ls => fail_with_bad_children(ls, 1)
          }
          case _ => fail_with_bad_proof_structure()
        }
        case UnificationRules.Pick => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.Pick(label, map)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case FailRules.AbduceBranch => node.kont match {
          case GuardedProducer(cond, bGoal) =>
            node.children match {
              case ::(if_true, ::(if_false, Nil)) => SuslikProofStep.AbduceBranch(label, cond, bGoal.label)
              case ls => fail_with_bad_children(ls, 2)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case OperationalRules.WriteRule => node.kont match {
          case ChainedProducer(ChainedProducer(PrependProducer(stmt@Store(_, _, _)), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.Write(label, stmt)
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
              case ::(head, Nil) => SuslikProofStep.WeakenPre(label, unused)
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
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(assignments), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) =>
                SuslikProofStep.PureSynthesis(label, is_final = true, assignments)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case UnfoldingRules.Open => node.kont match {
          case ChainedProducer(ChainedProducer(BranchProducer(Some(pred), fresh_vars, sbst, selectors), HandleGuard(_)), ExtractHelper(_)) =>
            SuslikProofStep.Open(label, pred, fresh_vars, sbst, selectors.toList)
          case _ => fail_with_bad_proof_structure()
        }
        case LogicalRules.SubstLeft => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.SubstL(label, map)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case UnificationRules.SubstRight => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.SubstR(label, map)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case OperationalRules.ReadRule => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(GhostSubstProducer(map), PrependProducer(stmt@Load(_, _, _, _))), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.Read(label, map, stmt)
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
                SuslikProofStep.AbduceCall(label, new_vars, f_pre, callePost, call, freshSub, freshToActual, f, head.goal.gamma)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case UnificationRules.HeapUnifyPure => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.HeapUnify(label, subst)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case UnificationRules.HeapUnifyUnfolding => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.HeapUnify(label, subst)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case UnificationRules.HeapUnifyBlock => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.HeapUnify(label, subst)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case UnificationRules.HeapUnifyPointer => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.HeapUnifyPointer(label, subst)
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
                    SuslikProofStep.FrameUnfold(label, h_pre, h_post)
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
                    SuslikProofStep.FrameUnfold(label, h_pre, h_post)
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
                    SuslikProofStep.FrameUnfold(label, h_pre, h_post)
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
                    SuslikProofStep.FrameUnfold(label, h_pre, h_post)
                }
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case UnfoldingRules.CallRule => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(subst),PrependProducer(call: Statements.Call)), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.Call(label, subst, call)
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
              case ::(head, Nil) => SuslikProofStep.Free(label, stmt, size)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case OperationalRules.AllocRule => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(GhostSubstProducer(map), PrependProducer(stmt@Statements.Malloc(_, _, _))), HandleGuard(_)), ExtractHelper(goal)) =>
            node.children match {
              case ::(head, Nil) =>
                SuslikProofStep.
                  Malloc(label, map, stmt)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }
        case UnfoldingRules.Close => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(UnfoldProducer(app, selector, asn, fresh_exist), IdProducer), HandleGuard(_)), ExtractHelper(_)) =>
            node.children match {
              case ::(head, Nil) =>
                SuslikProofStep.Close(label, app, selector, asn, fresh_exist)
              case ls => fail_with_bad_children(ls, 1)
            }
        }
        case LogicalRules.StarPartial => node.kont match {
          case ChainedProducer(ChainedProducer(IdProducer, HandleGuard(_)), ExtractHelper(goal)) =>
            val new_pre_phi = extendPure(goal.pre.phi, goal.pre.sigma)
            val new_post_phi = extendPure(goal.pre.phi && goal.post.phi, goal.post.sigma)

            node.children match {
              case ::(head, Nil) =>
                SuslikProofStep.StarPartial(label, new_pre_phi, new_post_phi)
              case ls => fail_with_bad_children(ls, 1)
            }
          case _ => fail_with_bad_proof_structure()
        }

        case UnificationRules.PickCard => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.PickCard(label, map)
              case ls => fail_with_bad_children(ls, 1)
            }
        }
        case UnificationRules.PickArg => node.kont match {
          case ChainedProducer(ChainedProducer(ChainedProducer(SubstProducer(map), IdProducer), HandleGuard(_)), ExtractHelper(goal)) =>
            node.children match {
              case ::(head, Nil) => SuslikProofStep.PickArg(label, map)
              case ls => fail_with_bad_children(ls, 1)
            }
        }
      }

      ProofTree(rule, node.children.map(visit).toList)
    }

    val rest = visit(node)
    ProofTree(Init(None, node.goal), List(rest))
  }

  /**
    *
    * Finalizes the branches abduced by applications of the AbduceBranch rule.
    *
    * Consider in the left diagram, an AbduceBranch node B with children C (true case) and D (false case), and
    * intended branch destination A. This procedure inserts a new Branch node E with A as its true case child; the
    * inserted node E is meant to denote a finalized branching point.
    *
    *           D---            D---    D---
    *          /       =>      /       /
    * --A-----B-C---        --E-A-----B-C---
    *
    * @param node the root node of the tree
    * @return a copy of the tree with finalized branches inserted
    */
    def finalize_branches(node: ProofTree[SuslikProofStep]): ProofTree[SuslikProofStep] = {
      def collect_branch_abductions(node: ProofTree[SuslikProofStep], abductions: Set[ProofTree[SuslikProofStep]] = Set.empty): Set[ProofTree[SuslikProofStep]] = {
        val abductions1 = node.rule match {
          case ab:AbduceBranch => abductions + node
          case _ => abductions
        }
        node.children.foldLeft(abductions1) { case (a, n) => collect_branch_abductions(n, a) }
      }
      def apply_branch_abductions(abductions: Set[ProofTree[SuslikProofStep]])(node: ProofTree[SuslikProofStep]): ProofTree[SuslikProofStep] = {
        node.rule.label match {
          case Some(label) =>
            abductions.find(_.rule.asInstanceOf[AbduceBranch].bLabel == label) match {
              case Some(ab@ProofTree(AbduceBranch(_, cond, bLabel), _)) =>
                val List(ifTrue, ifFalse) = ab.children
                val ifTrue1 = node.copy(children = node.children.map(apply_branch_abductions(abductions)))
                val ifFalse1 = apply_branch_abductions(abductions)(ifFalse)
                ProofTree(Branch(None, cond), List(ifTrue1, ifFalse1))
              case None =>
                node.copy(children = node.children.map(apply_branch_abductions(abductions)))
            }
          case None =>
            node.copy(children = node.children.map(apply_branch_abductions(abductions)))
        }
      }
      apply_branch_abductions(collect_branch_abductions(node))(node)
    }
}