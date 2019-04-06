package org.tygus.suslik.util

/**
  * @author Ilya Sergey
  */

object OtherUtil {
  // Todo: move to utils. Doesn't scala has same thing built in somewhere?
  class Accumulator[T]{
    private var elements:List[T] = Nil

    def put(elem:T):Unit={
      elements = elements ++ List(elem)
    }

    def get:List[T] = elements
  }
}
