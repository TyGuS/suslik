package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.Types.VSTType
import org.tygus.suslik.certification.targets.vst.logic.Expressions.{ProofCExpr, ProofCIfThenElse}
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.{PureFormula, VSTPredicate}
import org.tygus.suslik.certification.translation.{CardConstructor, CardNull, CardOf}
import org.tygus.suslik.certification.traversal.Step.DestStep
import org.tygus.suslik.certification.traversal.{ProofTree, ProofTreePrinter}
import org.tygus.suslik.language.{Ident, PrettyPrinting}


sealed abstract class VSTProofStep extends DestStep {}

object VSTProofStep {
  implicit object ProofTreePrinter extends ProofTreePrinter[VSTProofStep] {
    override def pp(tree: ProofTree[VSTProofStep]): String = tree.step match {
      case rule@ForwardIf => rule.pp ++ "\n" ++ rule.branch_strings(tree.children)
      case rule@ForwardIfConstructor(_,_,_) => tree.step.pp ++ "\n" ++ rule.branch_strings(tree.children)
      case _ => tree.step.pp ++ "\n" ++ tree.children.map(pp).mkString("\n")
    }
  }



  case object TentativeEntailer extends VSTProofStep {
    override def pp: String = s"ssl_entailer."
  }

  /**
    * Step capturing open rules on a predicate.
    * @param card_variable primary variable tracking the cardinality of the predicate (i.e _alpha in lseg x s _alpha)
    * @param predicate predicate being case analysed
    * @param branches
    */
  case class ForwardIfConstructor(
                                   card_variable: String,
                                   predicate: VSTPredicate,
                                   branches: List[((CardConstructor, List[String]), Expressions.ProofCExpr, List[String])]
                                 ) extends VSTProofStep {

    def branch_strings(children : List[ProofTree[VSTProofStep]]): String = {
      val branches = this.branches.zip(children).map({ case ((clause, selector, args), value) => (clause, selector, args, value)})
      def constructor_prop(cons: CardConstructor): String = {
        val cons_name = predicate.constructorName(cons)
        cons match {
          case CardNull => s"${card_variable} = ${cons_name}"
          case CardOf(args) => s"exists ${args.mkString(" ")}, ${card_variable} = ${cons_name} ${args.mkString(" ")}"
        }
      }
      val predicate_name = predicate.name
      branches match {
        case Nil => ""
        case _ =>
          "\n" ++ branches.map(
            { case ((cons, cons_args), expr, args, branch) =>
              " - {\n" ++
                s"assert_PROP (${constructor_prop(cons)}) as ssl_card_assert. { entailer!; ssl_dispatch_card. }\n" ++
                s"ssl_card ${predicate_name} ssl_card_assert ${cons_args.mkString(" ")}.\n" ++
                s"assert_PROP (${expr.pp}). { entailer!. }\n" ++
                (args match {
                  case Nil => ""
                  case args => s"Intros ${args.mkString(" ")}.\n"
                }) ++
                ProofTreePrinter.pp(branch) ++
                "\n}"
            }
          ).mkString("\n")
      }
    }

    override def pp: String = {
      "forward_if."
    }
  }

  case object ForwardIf extends VSTProofStep {
    def branch_strings (children: List[ProofTree[VSTProofStep]]) = {
      val branches = children
      branches match {
        case Nil => ""
        case _ => "\n" ++ branches.map(ls => " - {\n" ++ ProofTreePrinter.pp(ls) ++ "\n}").mkString("\n")
      }
    }
    override def pp: String = {
      "forward_if."
    }
  }

  case object Forward extends VSTProofStep {
    override def pp: String = s"forward."
  }

  case class ForwardTernary(ternary_expr: ProofCIfThenElse) extends VSTProofStep {
    override def pp: String = s"ssl_forward_write_ternary (${ternary_expr.pp_as_c_value});\ntry (forward; entailer!; ssl_reflect_boolean)."
  }

  case class Intros(variables: List[(Ident, VSTType)]) extends VSTProofStep {
    override def pp: String = {
      s"Intros ${variables.map(_._1).mkString(" ")}."
    }
  }

  case class IntrosTuple(variables: List[(Ident, VSTType)]) extends VSTProofStep {
    override def pp =  variables match {
      case Nil => ""
      case ::((variable, _), Nil) =>
        s"Intros ${variable}."
      case _ =>
        def to_destruct_pattern(base: Option[String])(ls: List[(Ident, VSTType)]): String = {
          (base, ls) match {
            case (None, ::((vara, _), ::((varb, _), rest))) => to_destruct_pattern(Some(s"[${vara} ${varb}]"))(rest)
            case (Some(base), ::((vara, _), rest)) =>
              to_destruct_pattern(Some(s"[${base} ${vara}]"))(rest)
            case (Some(base), Nil) => base
          }
        }
        val destruct_pattern: String = to_destruct_pattern(None)(variables)
        s"let ret := fresh vret in Intros ret; destruct ret as ${destruct_pattern}."
    }
  }

  case class ValidPointerOrNull(variable: Ident) extends VSTProofStep {
    override def pp: String = s"assert_PROP (is_pointer_or_null ${variable}). { entailer!. }"
  }

  case class ValidPointer(variable: Ident) extends VSTProofStep {
    override def pp: String = s"assert_PROP (isptr ${variable}). { entailer!. }"
  }

  case class ForwardCall(args: List[ProofCExpr]) extends VSTProofStep {
    override def pp: String = s"forward_call (${args.map(_.pp).mkString(", ")})."
  }

  case class Rename(old_name: Ident, new_name: Ident) extends VSTProofStep {
    override def pp: String = s"try rename ${old_name} into ${new_name}."
  }

  case class Exists(variable: Expressions.ProofCExpr) extends VSTProofStep {
    override def pp: String = s"Exists ${variable.pp}."
  }

  case class Free(variable: Ident, sz: Int) extends VSTProofStep {
    override def pp: String = s"forward_call (tarray (Tunion _sslval noattr) ${sz}, ${variable})."
  }

  case class Malloc(size: Int) extends VSTProofStep {
    override def pp: String = s"forward_call (tarray (Tunion _sslval noattr) ${size})."
  }

  case class AssertPropSubst(variable: Ident, expr: Expressions.ProofCExpr) extends VSTProofStep {
    override def pp: String = s"let ssl_var := fresh in assert_PROP(${variable} = ${expr.pp}) as ssl_var; try rewrite ssl_var in *. { entailer!. }"
  }

  case class AssertProp(expr: PureFormula) extends VSTProofStep {
    override def pp: String = s"assert_PROP(${expr.pp}). { entailer!. }"
  }

  case object Qed extends VSTProofStep {
    override def pp: String = ""
  }

  case class UnfoldRewrite(rewrite_name: String, constructor_args: List[Option[ProofCExpr]]) extends VSTProofStep {
    def pp_o_expr (expr: Option[ProofCExpr]) : String = expr match {
      case None => "_"
      case Some(expr) => expr.pp
    }
    override def pp: String =
      s"rewrite (${rewrite_name} ${constructor_args.map(pp_o_expr).mkString(" ")}) at 1."
  }

  case object ForwardEntailer extends VSTProofStep {
    override def pp: String = s"forward; entailer!."
  }

}