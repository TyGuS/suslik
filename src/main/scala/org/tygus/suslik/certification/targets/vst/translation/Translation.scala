package org.tygus.suslik.certification.targets.vst.translation


import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Proof.{Proof, VSTPredicate}
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Proof
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.synthesis.IdProducer.ruleAssert
import org.tygus.suslik.synthesis.{AppendProducer, BranchProducer, ChainedProducer, ConstProducer, ExtractHelper, GhostSubstProducer, GuardedProducer, HandleGuard, IdProducer, PartiallyAppliedProducer, PrependFromSketchProducer, PrependProducer, SeqCompProducer, StmtProducer, SubstProducer, UnfoldProducer}

import scala.annotation.tailrec
import scala.collection.immutable

object Translation {

  case class TranslationException(msg: String) extends Exception(msg)

  def fail_with(msg: String) = throw TranslationException(msg)


  /** Implementation of a state monad where the state is a stack of elements */
  case class State[S,A](f: List[S] => (A, List[S])) {

    /** map = fmap */
    def map[B](g: A => B): State[S, B] =
      State(s => {
        val (a, t) = f(s)
        (g(a), t)
      })

    /** flatMap = >>= */
    def flatMap[B](g: A => State[S, B]): State[S, B] =
      State(s => {
        val (a, t) = f(s)
        g(a).f(t)
      })


    /** push an element onto the state */
    def push (s:S) : State[S, Unit] = {
      State(ss => ((), s +: ss))
    }

    /** push multiple values onto the state, in such a way that is equivalent to iterating through the list and pushing them on individually */
    def push_multi (s:List[S]) : State[S, Unit] = {
      @tailrec
      def rev_cat[C](ls: List[C])(acc: List[C]) : List[C] = ls match {
        case Nil => acc
        case ::(head,tail) => rev_cat(tail)(head +: acc)
      }
      State(ss => ((), rev_cat(s)(ss)))
    }

    /** pop a value off the stack */
    def pop : State[S, S] = State {
      case Nil => fail_with("State monad ran out of state")
      case ::(head, tl) => (head, tl)
    }

    /** run the state monad to get a value */
    def eval(s: List[S]): A = f(s)._1
  }


  def translate(root: CertTree.Node, proc: Procedure, env: Environment): Nothing   = {
    val procedure = CTranslation.translate_function(proc, root.goal.gamma)
    val spec = ProofTranslation.translate_conditions(procedure)(root.goal)
    println(procedure.pp)
    println(spec.pp)
    val predicates: List[VSTPredicate] = env.predicates.map({ case (_, predicate) =>
      ProofTranslation.translate_predicate(env)(predicate)
    }).toList

    predicates.foreach(v => println(v.pp))
    println(root.goal.gamma)

    //translate_cont(root.children, root.kont)

    // translate body into VST types, and build context of variables
    // var (body, ctx) = CTranslation.translate_body(proc.f, proc.body, root.goal.gamma)
    // use this to build a C-encoding of the synthesized function
    // var body_string = print_as_c_program(proc.f, body, ctx)
    // print(body_string)


    // translate predicates
    // translate proof
    ???
  }
}
