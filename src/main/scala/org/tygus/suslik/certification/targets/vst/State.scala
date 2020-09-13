package org.tygus.suslik.certification.targets.vst

import org.tygus.suslik.certification.targets.vst.translation.Translation.fail_with

import scala.annotation.tailrec

/** Implementation of a state monad where the state is a stack of elements */
case class State[S, A](f: List[S] => (A, List[S])) {

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
  def eval(s: List[S]): A = f(s)._1
}

object State {
  /** return value  */
  def ret[S, A]  (v: A ) : State[S, A] = State(ls => (v ,ls))

  /** push an element onto the state */
  def push[S] (s :S) : State[S, Unit] = {
    State(ss => ((), s +: ss))
  }

  /** push multiple values onto the state, in such a way that is equivalent to iterating through the list and pushing them on individually */
  def push_multi[S] (s :List[S]) : State[S, Unit] = {
    @tailrec
    def rev_cat[C](ls: List[C])(acc: List[C]) : List[C] = ls match {
      case Nil => acc
      case ::(head ,tail) => rev_cat(tail)(head +: acc)
    }
    State(ss => ((), rev_cat(s)(ss)))
  }

  /** pop a value off the stack */
  def pop[S] : State[S, S] = State {
    case Nil => fail_with("State monad ran out of state")
    case ::(head, tl) => (head, tl)
  }

  def mapM[B,S,A] (ls: List[B]) (f: B => State[S,A]) : State[S,List[A]] =
    ls match {
      case Nil => State.ret(Nil)
      case ::(head0, tail0) => for {
        head <- f(head0)
        tail <- mapM(tail0)(f)
      } yield (head :: tail)
    }

}