package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.Types.VSTType
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.CardConstructor
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



  case object Entailer extends VSTProofStep {
    override def pp: String = s"entailer!."
  }

  case class ForwardIfConstructor(
                                   card_variable: String,
                                   predicate_name: String,
                                   branches: List[((Ident, CardConstructor, List[String]), Expressions.ProofCExpr, List[String])]
                                 ) extends VSTProofStep {

    def branch_strings(children : List[ProofTree[VSTProofStep]]): String = {
      val branches = this.branches.zip(children).map({ case ((clause, selector, args), value) => (clause, selector, args, value)})
      def constructor_prop(cons_name: Ident, cons: CardConstructor): String = cons match {
        case ProofTerms.CardNull => s"${card_variable} = ${cons_name}"
        case ProofTerms.CardOf(args) => s"exists ${args.mkString(" ")}, ${card_variable} = ${cons_name} ${args.mkString(" ")}"
      }
      branches match {
        case Nil => ""
        case _ =>
          "\n" ++ branches.map(
            { case ((cons_name, cons, cons_args), expr, args, ls) =>
              " - {\n" ++
                s"assert_PROP (${constructor_prop(cons_name, cons)}) as ssl_card_assert. { entailer!; ssl_dispatch_card. }\n" ++
                s"ssl_card ${predicate_name} ssl_card_assert ${cons_args.mkString(" ")}.\n" ++
                s"assert_PROP (${expr.pp}). { entailer!. }\n" ++
                (args match {
                  case Nil => ""
                  case args => s"Intros ${args.mkString(" ")}.\n"
                }) ++
                ProofTreePrinter.pp(ls) ++
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

  case class Intros(variables: List[(Ident, VSTType)]) extends VSTProofStep {
    override def pp: String = {
      s"Intros ${variables.map(_._1).mkString(" ")}."
    }
  }

  case class IntrosTuple(variables: List[(Ident, VSTType)]) extends VSTProofStep {
    variables match {
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

  case class ForwardCall(args: List[Ident]) extends VSTProofStep {
    override def pp: String = s"forward_call (${args.mkString(", ")})."
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
    override def pp: String = s"let ssl_var := fresh in assert_PROP(${variable} = ${expr.pp}) as ssl_var; try rewrite ssl_var. { entailer!. }"
  }

  case object Qed extends VSTProofStep {
    override def pp: String = ""
  }

  case class Unfold(predicate: ProofTerms.VSTPredicate, args: Int, cardinality: Expressions.ProofCExpr) extends VSTProofStep {
    override def pp: String =
      s"simpl (${predicate.name} ${List.iterate("_", args)(v => v).mkString(" ")} (${cardinality.pp})) at 1."

  }

  case object ForwardEntailer extends VSTProofStep {
    override def pp: String = s"forward; entailer!."
  }

}