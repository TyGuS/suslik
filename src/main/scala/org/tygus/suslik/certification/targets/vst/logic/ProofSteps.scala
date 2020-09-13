package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.clang.PrettyPrinting
import ProofTerms.CardConstructor
import org.tygus.suslik.certification.targets.vst.logic.ProofTerms.Expressions.ProofCExpr
import org.tygus.suslik.certification.targets.vst.logic.ProofTypes.VSTProofType
import org.tygus.suslik.language.Ident

sealed abstract class ProofSteps extends PrettyPrinting {

  def to_validity_assertion(var_name: Ident, var_type: VSTProofType) : Option[ProofSteps] = {
    var_type match {
      case ProofTypes.CoqParamType(ty) => None
      case ProofTypes.CoqPtrType => None
      case ProofTypes.CoqIntType => None
      case ProofTypes.CoqCardType(pred_type) => None
      case ProofTypes.CoqListType(elem, length) => None
    }
  }

}

object ProofSteps {
  case class Entailer(next: ProofSteps) extends ProofSteps {
    override def pp: String = s"entailer!.\n${next.pp}"
  }

  case class ForwardIfConstructor(
                                   card_variable: String,
                                   predicate_name: String,
                                   branches: List[((Ident, CardConstructor, List[String]), ProofCExpr, List[String], ProofSteps)]
                                 ) extends ProofSteps {
    override def pp: String = {
      def constructor_prop (cons_name: Ident, cons: CardConstructor) : String = cons match {
        case ProofTerms.CardNull => s"${card_variable} = ${cons_name}"
        case ProofTerms.CardOf(args) => s"exists ${args.mkString(" ")}, ${card_variable} = ${cons_name} ${args.mkString(" ")}"
      }

      val branch_strings =
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
                  ls.pp ++
                  "\n}"
              }
            ).mkString("\n")
        }
      "forward_if." ++ branch_strings
    }
  }

  case class ForwardIf(branches: List[ProofSteps]) extends ProofSteps {
    override def pp: String = {
      val branch_strings =
        branches match {
          case Nil => ""
          case _ => "\n" ++ branches.map(ls => " - {\n" ++ ls.pp ++ "\n}").mkString("\n")
        }
      "forward_if." ++ branch_strings
    }
  }

  case class Forward(next:ProofSteps) extends ProofSteps {
    override def pp: String = s"forward.\n${next.pp}"
  }

  case class Intros(variables: List[(Ident, VSTProofType)], next: ProofSteps) extends ProofSteps {
    override def pp: String = {
      val extra_assertions =
        variables.flatMap({ case (var_name, var_type) =>
          to_validity_assertion(var_name, var_type)
        }) match {
          case Nil => ""
          case ls => "\n" ++ ls.map(_.pp).mkString(".\n")
        }
      s"Intros ${variables.map(_._1).mkString(" ")}." ++ extra_assertions ++ s"\n${next.pp}"
    }
  }

  case class ValidPointerOrNull(variable: Ident,next: ProofSteps) extends ProofSteps {
    override def pp: String = s"assert_PROP (is_pointer_or_null ${variable}). { entailer!. }\n${next.pp}"
  }

  case class ValidPointer(variable: Ident,next: ProofSteps) extends ProofSteps {
    override def pp: String = s"assert_PROP (isptr ${variable}). { entailer!. }\n${next.pp}"
  }

  case class ForwardCall(args: List[Ident], next: ProofSteps) extends ProofSteps {
    override def pp: String = s"forward_call (${args.mkString(", ")}).\n${next.pp}"
  }

  case class Rename(old_name: Ident, new_name: Ident, next: ProofSteps) extends ProofSteps {
    override def pp: String = s"try rename ${old_name} into ${new_name}.\n${next.pp}"
  }

  case class Exists(variable: Ident, next: ProofSteps) extends ProofSteps {
    override def pp: String = s"Exists ${variable}.\n${next.pp}"
  }

  case class Free(variable: Ident, sz: Int, next: ProofSteps) extends ProofSteps {
    override def pp: String = s"forward_call (tarray (Tunion _sslval noattr) ${sz}, ${variable}).\n${next.pp}"
  }

  case class AssertPropSubst(variable: Ident, expr: ProofCExpr, next: ProofSteps) extends ProofSteps {
    override def pp: String = s"let ssl_var := fresh in assert_PROP(${variable} = ${expr.pp_as_ptr_value}) as ssl_var; try rewrite ssl_var. { entailer!. }\n${next.pp}"
  }

  case object Qed extends ProofSteps {
    override def pp: String = ""
  }
}