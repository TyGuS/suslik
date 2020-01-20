package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.SSLException
import org.tygus.suslik.synthesis.SynthesisException
import org.tygus.suslik.synthesis.SymbolicExecutionError

/**
  * @author Ilya Sergey
  */

trait RuleUtils {

  val exceptionQualifier: String

  case class SynthesisRuleException(msg: String) extends SSLException(exceptionQualifier, msg)

  def ruleAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisRuleException(msg)
  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)
  def symExecAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SymbolicExecutionError(msg)

  def nubBy[A,B](l:List[A], p:A=>B):List[A] =
  {
    def go[A,B](l:List[A], p:A=>B, s:Set[B], acc:List[A]):List[A] = l match
    {
      case Nil => acc.reverse
      case x::xs if s.contains(p(x)) => go(xs,p,s,acc)
      case x::xs                     => go(xs,p,s+p(x),x::acc)
    }
    go(l,p,Set.empty,Nil)
  }
}

