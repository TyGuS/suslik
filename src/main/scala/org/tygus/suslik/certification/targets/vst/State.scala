package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.targets.vst.translation.Translation.fail_with

import scala.annotation.tailrec

/** Implementation of a state monad where the state is a stack of elements */
case class State[S, A](f: Seq[S] => (A, Seq[S])) {

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


  /** run the state monad to get a value */
  def eval(s: Seq[S]): A = f(s)._1
}

object State {
  /** return value  */
  def ret[S, A]  (v: A ) : State[S, A] = State(ls => (v ,ls))

  /** push an element onto the state */
  def push[S] (s :S) : State[S, Unit] = {
    State(ss => ((), s +: ss))
  }

  /** push multiple values onto the state, in such a way that is equivalent to iterating through the list and pushing them on individually */
  def push_multi[S] (s :Seq[S]) : State[S, Unit] = {
    @tailrec
    def rev_cat[C](ls: Seq[C])(acc: Seq[C]) : Seq[C] = ls match {
      case Seq(head, tail@_*) => rev_cat(tail)(head +: acc)
      case _ => acc
    }
    State(ss => ((), rev_cat(s)(ss)))
  }

  /** pop a value off the stack */
  def pop[S] : State[S, S] = State {
    case Seq(head, tl@_*) => (head, tl)
    case _ => fail_with("State monad ran out of state")
  }

  def mapM[B,S,A] (ls: Seq[B]) (f: B => State[S,A]) : State[S,Seq[A]] =
    ls match {
      case Seq(head0, tail0@_*) => for {
        head <- f(head0)
        tail <- mapM(tail0)(f)
      } yield head +: tail
      case _ => State.ret(Seq.empty)
    }

}