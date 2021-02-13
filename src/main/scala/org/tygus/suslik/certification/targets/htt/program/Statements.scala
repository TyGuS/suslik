package org.tygus.suslik.certification.targets.htt.program

import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.traversal.Step.DestStep

object Statements {
  sealed abstract class CStatement extends DestStep

  case object CError extends CStatement {
    override def pp: String = "ret tt"
  }

  case object CSkip extends CStatement {
    override def pp: String = "ret tt"
  }

  case class CMalloc(to: CVar, tpe: HTTType, sz: Int = 1) extends CStatement {
    override def pp: String = s"${to.pp} <-- allocb null $sz;"
  }

  case class CFree(v: CVar, offset: Int) extends CStatement {
    override def pp: String =
      if (offset > 0) {
        s"dealloc (${v.pp} .+ $offset);;"
      } else {
        s"dealloc ${v.pp};;"
      }
  }

  case class CLoad(to: CVar, tpe: HTTType, from: CVar, offset: Int = 0) extends CStatement {
    override def pp: String = {
      val f = if (offset <= 0) from.pp else s"(${from.pp} .+ $offset)"
      s"${to.pp} <-- @read ${tpe.pp} $f;"
    }
  }

  case class CStore(to: CVar, offset: Int, e: CExpr) extends CStatement {
    override def pp: String = {
      val t = if (offset <= 0) to.pp else s"(${to.pp} .+ $offset)"
      s"$t ::= ${e.pp};;"
    }
  }

  case class CCall(fun: CVar, args: Seq[CExpr]) extends CStatement {
    override def pp: String = s"${fun.pp} (${args.map(_.pp).mkString(", ")});;"
  }

  case class CIf(selectors: Seq[CExpr]) extends CStatement

  case class CGuarded(cond: CExpr) extends CStatement

  case object Noop extends CStatement
}
