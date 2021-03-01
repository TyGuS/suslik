package org.tygus.suslik.certification.targets.iris.heaplang

import org.tygus.suslik.certification.targets.iris.translation.ProgramPrinter
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.certification.traversal.Step.DestStep
import org.tygus.suslik.language.PrettyPrinting

/** Encoding of HeapLang expressions.
 *
 * HeapLang does distinguish between statements and expressions: everything is an expression.
 * We model only a very restricted subset of HeapLang.
 * */
object Expressions {

  sealed abstract class HExpr extends DestStep

  /** Literals */
  class HLit(repr: String) extends HExpr {
    override def pp: String = s"#${repr}"
  }

  case class HLitUnit() extends HLit("()") {}

  case class HLitInt(value: Int) extends HLit(value.toString)

  case class HLitOffset(off: Int) extends HLit(off.toString) {
    override def pp: String = s"$off"
  }

  case class HLitBool(value: Boolean) extends HLit(value.toString)

  case class HLitLoc(loc: Int) extends HLit(loc.toString) {
    override def pp: String = if(loc == 0) "#null_loc" else super.pp
  }

  case class HSetLiteral(elems: List[HExpr]) extends HExpr {
    override def pp: String =
      s"[${elems.map(_.pp).mkString("; ")}]"
  }
  /** Variables */
  case class HProgVar(name: String) extends HExpr {
    override def pp: String = s""""${name}""""
  }

  /** Operators */
  sealed abstract class HUnOp extends PrettyPrinting

  object HOpNot extends HUnOp {
    override def pp: String = "~"
  }

  object HOpUnaryMinus extends HUnOp {
    override def pp: String = "-"
  }

  sealed abstract class HBinOp extends PrettyPrinting

  object HOpPlus extends HBinOp {
    override def pp: String = "+"
  }

  object HOpUnion extends HBinOp {
    override def pp: String = "++"
  }

  object HOpMinus extends HBinOp {
    override def pp: String = "-"
  }

  object HOpMultiply extends HBinOp {
    override def pp: String = "*"
  }

  object HOpEq extends HBinOp {
    override def pp: String = "="
  }

  object HOpSetEq extends HBinOp {
    override def pp: String = "="
  }

  object HOpLt extends HBinOp {
    override def pp: String = "<"
  }

  object HOpLe extends HBinOp {
    override def pp: String = "≤"
  }

  object HOpOffset extends HBinOp {
    override def pp: String = "+ₗ"
  }

  /** Operations */
  case class HUnaryExpr(op: HUnOp, e: HExpr) extends HExpr {
    override def pp: String = s"${op.pp} ${e.pp}"
  }

  case class HBinaryExpr(op: HBinOp, left: HExpr, right: HExpr) extends HExpr {
    override def pp: String = s"${left.pp} ${op.pp} ${right.pp}"
  }

  /** Condition */
  case class HIfThenElse(cond: HExpr, trueBranch: HExpr, falseBranch: HExpr) extends HExpr {
    override def pp: String =
      s"""|if: (${cond.pp}) then (
         |${trueBranch.pp}
         |) else (
         |${falseBranch.pp}
         |)""".stripMargin
  }

  /** Let-bindings. We use HeapLang's syntactic sugar over lambdas. */
  case class HLet(x: HExpr, lhs: HExpr, in: HExpr) extends HExpr {
    override def pp: String =
      s"""|let: ${x.pp} := ${lhs.pp} in
          |${in.pp}""".stripMargin
  }

  case class HSeqComp(s1: HExpr, s2: HExpr) extends HExpr {
    override def pp: String =
      s"""|${s1.pp} ;;
          |${s2.pp}""".stripMargin
  }

  /** Heap manipulation */
  case class HLoad(e: HExpr) extends HExpr {
    override def pp: String = s"! (${e.pp})"
  }
  case class HStore(lhs: HExpr, rhs: HExpr) extends HExpr {
    override def pp: String = s"(${lhs.pp}) <- (${rhs.pp})"
  }
  case class HFree(e: HExpr) extends HExpr {
    override def pp: String = s"Free (${e.pp})"
  }
  case class HAlloc(e: HExpr) extends HExpr {
    override def pp: String = s"Alloc (${e.pp})"
  }
  case class HAllocN(n: HExpr, e: HExpr) extends HExpr {
    override def pp: String = s"AllocN (${n.pp}) (${e.pp})"
  }
  case class HCall(name: HExpr, params: Seq[HExpr], selfCall: Boolean = true) extends HExpr {
    override def pp: String =
      // if it's a selfCall, we need to print the function name in quotes, otherwise no quotes
      s"${if(selfCall) name.pp else name.asInstanceOf[HProgVar].name} ${params.map(p => p.pp).mkString(" ")}"
  }

  case class HFunDef(name: String, params: Seq[HProgVar], body: ProofTree[HExpr]) extends PrettyPrinting {
    override def pp: String = {
      s"""
        |Definition ${name} : val :=
        |rec: "${name}" ${params.map(p => p.pp).mkString(" ")} :=
        |${ProgramPrinter.pp(body)}.
        |""".stripMargin
    }
  }

  /** Artificial statements to match SSL proof rules. */
  case class HIf(selectors: Seq[HExpr]) extends HExpr

  case class HGuarded(cond: HExpr) extends HExpr

  case object HNoOp extends HExpr

}
