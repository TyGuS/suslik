package org.tygus.suslik.certification.targets.vst.clang

import org.tygus.suslik.certification.{ClangHeaderOutput, ClangOutput}
import org.tygus.suslik.certification.targets.vst.Types.VSTCType
import org.tygus.suslik.certification.targets.vst.logic.Expressions.CLangExpr
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.FormalSpecification
import org.tygus.suslik.certification.traversal.Step.DestStep
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter}
import org.tygus.suslik.language.PrettyPrinting

/** Encoding of C statements */
object Statements {

  implicit object ProofTreePrinter extends ProofTreePrinter[StatementStep] {
    override def pp(tree: ProofTree[StatementStep]): String = tree.step match {
      case CIf(cond) =>
        s"if (${cond.pp_as_clang_expr}) {\n" +
          s"${pp(tree.children(0))}" +
          s"} else {\n" +
          s"${pp(tree.children(1))}" +
          s"}"
      case CElif(conds) =>
        val branches = conds.zip(tree.children)
        val (first_cond, first_body) = branches.head
        val rest = branches.tail
        val rest_cases = rest.reverse match {
          case ::((_, last_child), remaining) =>
            remaining.foldLeft(s"\nelse {\n${pp(last_child)}}")({case (str, (cond, body)) =>
              s"\nelse if (${cond.pp_as_clang_expr}) {\n${pp(body)}}${str}"
            })
        }
        s"if (${first_cond.pp_as_clang_expr}) {\n${pp(first_body)}}${rest_cases}"
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

  case class CWriteInt(to: String, value: CLangExpr, offset: Int = 0) extends StatementStep {
    override def pp : String =
      s"WRITE_INT(${to}, ${offset}, ${value.pp_as_clang_expr});"
  }

  case class CWriteLoc(to: String, value: CLangExpr, offset: Int = 0) extends StatementStep {
    override def pp : String =
      s"WRITE_LOC(${to}, ${offset}, ${value.pp_as_clang_expr});"
  }

  /** encoding of a function call f(args) */
  case class CCall(fun: String, args: Seq[CLangExpr]) extends StatementStep {
    override def pp: String = s"${fun}(${args.map(_.pp_as_clang_expr).mkString(", ")});"
  }

  /** Encoding of statement
    * if (cond) { tb } else { eb }
    *  */
  case class CIf(cond: CLangExpr) extends StatementStep {
    override def pp : String =
      s"if(${cond.pp_as_clang_expr})"
  }

  /** Encoding of statement
    * if (cond1) { tb } else if(cond2) { eb } else (cond3)
    *  */
  case class CElif(cond: List[CLangExpr]) extends StatementStep {
    override def pp : String =
      cond match {
        case Nil => ???
        case ::(head, tl) =>
          s"if (${head.pp_as_clang_expr}) { ??? } ${
            tl.reverse match {
              case Nil => ???
              case ::(last, remaining) =>
                remaining.foldLeft("else { ??? }")((str, elt) =>
                s"else if (${elt.pp_as_clang_expr}) { ??? } ${str}"
                )
            }
          }"
      }
  }

  object CProcedureDefinition {
    val common_defs = """typedef union sslval {
                        |  int ssl_int;
                        |  void *ssl_ptr;
                        |} *loc;
                        |#define READ_LOC(x,y) (*(x+y)).ssl_ptr
                        |#define READ_INT(x,y) (*(x+y)).ssl_int
                        |#define WRITE_LOC(x,y,z) (*(x+y)).ssl_ptr = z
                        |#define WRITE_INT(x,y,z) (*(x+y)).ssl_int = z""".stripMargin


    def common_c_file (base_name: String): ClangOutput =
      ClangOutput(
        filename=s"${base_name}.c",
        name=base_name,
        s"""#include <stddef.h>
           |#include "${base_name}.h"
           |
           |loc vst_keep_my_damn_definitions = NULL;""".stripMargin
      )

    def common_c_header (base_name: String): ClangHeaderOutput =
      ClangHeaderOutput(
        filename=s"${base_name}.h",
        name=base_name,
        s"""#ifndef COMMON_H
           |#define COMMON_H
           |
           |${common_defs}
           |
           |#endif""".stripMargin
      )

    def c_prelude(common_defs_header_file: Option[String], helper_specs: List[FormalSpecification]) =
      s"""#include <stddef.h>
         |${
        common_defs_header_file match {
          case Some(header_file_name) => "#include \"" ++ header_file_name ++ ".h\""
          case None => ""
        }}
         |
         |extern void free(void *p);
         |extern void *malloc(size_t size);
         |
         |${common_defs_header_file match {
        case Some(value) => "" // have common defs, no need to include
        case None => common_defs
      }}
         |
        ${helper_specs.map(spec => s"|${spec.pp_as_c_decl}").mkString("\n")}
         |
         |""".stripMargin
  }

  /** Definition of a CProcedure */
  case class CProcedureDefinition(
                                   name: String,
                                   params: Seq[(String, VSTCType)],
                                   body: ProofTree[StatementStep],
                                   helper_specs: List[FormalSpecification]
                                 )  extends PrettyPrinting {

    def pp_with_common_defs(base_filename: String, common_predicates: List[ProofTerms.VSTPredicate]): String = {
      val body_string = ProofTreePrinter.pp(body)
      val function_def =
        s"void ${name}(${
          params.map({case (variable_name, variable_ty) =>
            s"${variable_ty.pp_as_ctype} ${variable_name}"
          }).mkString(", ")
        }) {\n${body_string}\n}\n"
      CProcedureDefinition.c_prelude(Some(base_filename), helper_specs) + function_def
    }


    override def pp: String = {
      val body_string = ProofTreePrinter.pp(body)
      val function_def =
        s"void ${name}(${
          params.map({case (variable_name, variable_ty) =>
            s"${variable_ty.pp_as_ctype} ${variable_name}"
          }).mkString(", ")
        }) {\n${body_string}\n}\n"

      CProcedureDefinition.c_prelude(None, helper_specs) + function_def
    }

  }

}
