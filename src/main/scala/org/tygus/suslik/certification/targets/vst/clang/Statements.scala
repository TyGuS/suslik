package org.tygus.suslik.certification.targets.vst.clang

import org.tygus.suslik.certification.targets.vst.clang.CTypes.{VSTCType}
import org.tygus.suslik.certification.targets.vst.clang.Expressions.{CExpr, CVar}
import org.tygus.suslik.logic.Specifications.GoalLabel

/** Encoding of C statements */
object Statements {

  /** pretty printing a VST C Statement returns a C embedding */
  sealed abstract class CStatement extends PrettyPrinting { }

  // skip
  case object CSkip extends CStatement {
    override def pp: String = {
      "return;"
    }
  }

  // ??
  case object CHole extends CStatement {
    override def pp: String = { ??? }
  }

  // assert false
  case object CError extends CStatement {
    override def pp: String = ???
  }

  // let to = malloc(n)
  case class CMalloc(to: CVar, tpe: VSTCType, sz: Int = 1) extends CStatement {
    override def pp: String =
      s"${tpe.pp} ${to.pp} = (${tpe.pp})malloc(${sz.toString} * sizeof(${tpe.pp}));"
  }

  // free(v)
  case class CFree(v: CVar) extends CStatement {
    override def pp: String = s"free(${v.pp});"
  }

  /** encoding of a load operation
    *  let to = *from.offset
    *  */
  case class CLoad(to: CVar, elem_ty: VSTCType, from: CVar,
                   offset: Int = 0) extends CStatement {
    override def pp: String =
      if (offset == 0) {
        s"${elem_ty.pp} ${to.pp} = *(${elem_ty.pp}*)${from.pp};"
      }else {
        s"${elem_ty.pp} ${to.pp} =  *((${elem_ty.pp}*)${from.pp} + ${offset.toString});"
      }
  }

  /** Encoding of a store operation
    * *to.offset = e */
  case class CStore(to: CVar, elem_ty: VSTCType, offset: Int, e: CExpr) extends CStatement {
    override def pp: String = {
      val cast = s"(${elem_ty.pp})"
      val ptr = s"(${elem_ty.pp}*)${to.pp}"
      if (offset == 0) {
        s"*${ptr} = ${cast} ${e.pp};"
      } else {
        s"*(${ptr} + ${offset.toString}) = ${cast} ${e.pp};"
      }
    }
  }

  /** encoding of a function call f(args) */
  case class CCall(fun: CVar, args: Seq[CExpr], companion: Option[GoalLabel]) extends CStatement {
    override def pp: String = s"${fun.pp}(${args.map(_.pp).mkString(", ")});"
  }

  /** Encoding of sequential composition
    *
    * s1; s2 */
  case class CSeqComp(s1: CStatement, s2: CStatement) extends CStatement {
    override def ppIndent(depth:  Int): String =
          s"${s1.ppIndent(depth)}\n${s2.ppIndent(depth)}"
  }

  /** Encoding of statement
    * if (cond) { tb } else { eb }
    *  */
  case class CIf(cond: CExpr, tb: CStatement, eb: CStatement) extends CStatement {
    override def ppIndent(depth: Int): String =
      s"${getIndent(depth)}if(${cond.pp}) {\n${tb.ppIndent(depth+1)}\n${getIndent(depth)}} else {\n${eb.ppIndent(depth+1)}\n${getIndent(depth)}}\n"
  }

  /**
    * Encoding of a statement:
    * assume cond { body } else { els }
    * */
  case class CGuarded(cond: CExpr, body: CStatement, els: CStatement, branchPoint: GoalLabel) extends CStatement {
    override def ppIndent(depth: Int): String =
      s"${getIndent(depth)}if(${cond.pp}) {\n${body.ppIndent(depth+1)}\n${getIndent(depth)}} else {\n${els.ppIndent(depth+1)}\n${getIndent(depth)}}\n"
  }

  /** Definition of a CProcedure */
  case class CProcedureDefinition(
                                   name: String,
                                   rt: VSTCType,
                                   params: Seq[(CVar, VSTCType)],
                                   body: CStatement
                                 )  extends PrettyPrinting {
    override def pp: String = {
      val body_string = body.ppIndent(1)
      val function_def =
        s"${rt.pp} ${name}(${
          params.map({case (variable_name, variable_ty) =>
            s"${variable_ty.pp} ${variable_name.pp}"
          }).mkString(", ")
        }) {\n${body_string}\n}\n"

      function_def
    }
  }

}
