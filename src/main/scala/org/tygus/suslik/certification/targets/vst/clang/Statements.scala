package org.tygus.suslik.certification.targets.vst.clang

import org.tygus.suslik.certification.targets.vst.Types.VSTCType
import org.tygus.suslik.certification.targets.vst.clang.Expressions.{CExpr, CVar}
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep
import org.tygus.suslik.certification.targets.vst.logic.VSTProofStep.{ForwardIf, ForwardIfConstructor}
import org.tygus.suslik.certification.targets.vst.translation.Translation.{TranslationException, fail_with}
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter}
import org.tygus.suslik.certification.traversal.Step.DestStep
import org.tygus.suslik.logic.Specifications.GoalLabel

/** Encoding of C statements */
object Statements {

  implicit object ProofTreePrinter extends ProofTreePrinter[StatementStep] {
    override def pp(tree: ProofTree[StatementStep]): String = tree.step match {
      case CIf(cond) =>
        s"if (${cond.pp} {\n" +
          s"${pp(tree.children(0))}" +
          s"} else {\n" +
          s"${pp(tree.children(1))}" +
          s"\n}"
      case _ => tree.step.pp ++ "\n" ++ tree.children.map(pp).mkString("\n")
    }
  }
  /** pretty printing a VST C Statement returns a C embedding */
  sealed abstract class StatementStep extends DestStep { }

  // skip
  case object CSkip extends StatementStep {
    override def pp: String = { "return;" }
  }

  // let to = malloc(n)
  case class CMalloc(to: String, sz: Int = 1) extends StatementStep {
    override def pp: String =
      s"loc ${to} = (loc) malloc(${sz.toString} * sizeof(loc));"
  }

  // free(v)
  case class CFree(v: String) extends StatementStep {
    override def pp: String = s"free(${v});"
  }

  case class CLoadInt(to: String, from: String, offset: Int = 0) extends StatementStep {
    override def pp: String = s"int ${to} = READ_INT(${from}, ${offset});"
  }

  case class CLoadLoc(to: String, from: String, offset: Int = 0) extends StatementStep {
    override def pp: String = s"loc ${to} = READ_LOC(${from}, ${offset});"
  }

  case class CWriteInt(to: CVar, value: CExpr, offset: Int = 0) extends StatementStep {
    override def pp : String =
      s"WRITE_INT(${to}, ${offset}, ${value.pp});"
  }

  case class CWriteLoc(to: CVar, value: CExpr, offset: Int = 0) extends StatementStep {
    override def pp : String =
      s"WRITE_LOC(${to}, ${offset}, ${value.pp});"
  }

  /** encoding of a function call f(args) */
  case class CCall(fun: String, args: Seq[CExpr]) extends StatementStep {
    override def pp: String = s"${fun}(${args.map(_.pp).mkString(", ")});"
  }

  /** Encoding of statement
    * if (cond) { tb } else { eb }
    *  */
  case class CIf(cond: CExpr) extends StatementStep {
    override def pp : String =
      s"if(${cond.pp})"
  }

  /** Definition of a CProcedure */
  case class CProcedureDefinition(
                                   name: String,
                                   params: Seq[(String, VSTCType)],
                                   body: ProofTree[StatementStep]
                                 )  extends PrettyPrinting {
    val c_prelude =
      """
        |#include <stddef.h>
        |
        |extern void free(void *p);
        |extern void *malloc(size_t size);
        |
        |typedef union sslval {
        |  int ssl_int;
        |  void *ssl_ptr;
        |} *loc;
        |#define READ_LOC(x,y) (*(x+y)).ssl_ptr
        |#define READ_INT(x,y) (*(x+y)).ssl_int
        |#define WRITE_LOC(x,y,z) (*(x+y)).ssl_ptr = z
        |#define WRITE_INT(x,y,z) (*(x+y)).ssl_int = z
        |
        |""".stripMargin

    override def pp: String = {
      val body_string = ProofTreePrinter.pp(body)
      val function_def =
        s"void ${name}(${
          params.map({case (variable_name, variable_ty) =>
            s"${variable_ty.pp_as_ctype} ${variable_name}"
          }).mkString(", ")
        }) {\n${body_string}\n}\n"

      c_prelude + function_def
    }
  }

}
