package org.tygus.suslik.synthesis.rules


import org.bitbucket.franck44.scalasmt.parser.{SMTLIB2Parser, SMTLIB2Syntax}
import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax._
import org.bitbucket.inkytonik.kiama.util.StringSource
import org.tygus.suslik.language.Expressions.{BinaryExpr, IntConst, LocConst, SetLiteral, Subst}
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.logic.{Gamma, PFormula, Specifications}
import org.tygus.suslik.synthesis.rules.Rules.{InvertibleRule, RuleResult, SynthesisRule}
import org.tygus.suslik.synthesis.{ExtractHelper, IdProducer, SubstMapProducer, SynthesisException}

import scala.collection.mutable
import scala.sys.process._
import scala.util.{Failure, Success}

object DelegatePureSynthesis {

  def typeToSMT(lType: SSLType): String = lType match {
    case IntType | LocType | CardType => "Int"
    case BoolType => "Bool"
    case IntSetType => "(Set Int)"
    case IntervalType => "Interval"
  }

  val empsetName = "empset"
  val typeConstants: Map[SSLType, List[Expressions.Expr]] = Map(
    IntType -> List(IntConst(0)),
    LocType -> List(IntConst(0)),
    IntSetType -> List(SetLiteral(List())),
    IntervalType -> List(Expressions.emptyInt),
    CardType -> List(IntConst(0))
  )
  val typeUnaries: Map[SSLType, List[Expressions.Expr => Expressions.Expr]] = Map(
    IntType -> List(e => e |+| IntConst(1)),
    LocType -> List(e => e |+| IntConst(1)),
    IntSetType -> List(),
    IntervalType -> List(),
    CardType -> List()
  )

  def toSmtExpr(c: Expressions.Expr, existentials: Map[Expressions.Var, String], sb: StringBuilder): Unit = c match {
    case v: Expressions.Var => sb ++= (if (existentials contains v) existentials(v) else v.name)
    case const: Expressions.Const => sb ++= const.pp
    case SetLiteral(elems) => elems.length match {
      case 0 => sb ++= empsetName
      case 1 =>
        sb ++= "(singleton "
        toSmtExpr(elems.head, existentials, sb)
        sb ++= ")"
      case _ =>
        sb ++= "(insert "
        for (e <- elems.dropRight(1)) {
          toSmtExpr(e, existentials, sb)
          sb ++= " "
        }
        sb ++= "(singleton "
        toSmtExpr(elems.last, existentials, sb)
        sb ++= "))"
    }
    case Expressions.BinaryExpr(op, left, right) => sb ++= "(" ++= (op match {
      case Expressions.OpAnd => "and"
      case Expressions.OpOr => "or"
      case Expressions.OpImplication => "=>"
      case Expressions.OpPlus => "+"
      case Expressions.OpMinus => "-"
      case Expressions.OpMultiply => "*"
      case Expressions.OpEq => "="
      case Expressions.OpBoolEq | Expressions.OpSetEq => "="
      case Expressions.OpLeq => "<="
      case Expressions.OpLt => "<"
      //Set ops all come from here: https://cvc4.github.io/sets-and-relations
      case Expressions.OpIn => "member"
      case Expressions.OpSubset => "subset"
      case Expressions.OpUnion => "union"
      case Expressions.OpDiff => "setminus"
      case Expressions.OpIntersect => "intersection"
      case Expressions.OpIntervalEq => "ieq"
      case Expressions.OpIntervalIn => "imember"
      case Expressions.OpIntervalUnion => "iunion"
      case Expressions.OpRange => "interval"
      case e => throw SynthesisException(s"Not supported: ${e.pp} (${e.getClass.getName})")  
    }) ++= " "
      toSmtExpr(left, existentials, sb)
      sb ++= " "
      toSmtExpr(right, existentials, sb)
      sb ++= ")"
    //case Expressions.OverloadedBinaryExpr(overloaded_op, left, right) =>
    case Expressions.UnaryExpr(op, arg) => sb ++= "(" ++= (op match {
      case Expressions.OpNot => "not"
      case Expressions.OpUnaryMinus => "-"
      case Expressions.OpLower => "lower"
      case Expressions.OpUpper => "upper"
    }) ++= " "
      toSmtExpr(arg, existentials, sb)
      sb ++= ")"
    case Expressions.IfThenElse(cond, left, right) =>
      sb ++= "(ite "
      toSmtExpr(cond, existentials, sb)
      sb ++= " "
      toSmtExpr(left, existentials, sb)
      sb ++= " "
      toSmtExpr(right, existentials, sb)
      sb ++= ")"
    case Expressions.Unknown(_,_,_) => sb ++= Expressions.eTrue.pp
    case e => throw SynthesisException(s"Not supported: ${e.pp} (${e.getClass.getName})")
  }

  def mkExistentialCalls(existentials: Set[Expressions.Var], otherVars: List[(Expressions.Var, SSLType)]): Map[Expressions.Var, String] =
    existentials.map { ex =>
      (ex, "(target_" + ex.name + (for (v <- otherVars) yield v._1.name).mkString(" ", " ", "") + ")")
    }.toMap

  def toSmt(phi: PFormula, existentials: Map[Expressions.Var, String], sb: StringBuilder): Unit = phi.conjuncts.size match {
    case 0 => sb ++= "true"
    case 1 => toSmtExpr(phi.conjuncts.head, existentials, sb)
    case _ => sb ++= "(and "
      for (c <- phi.conjuncts) {
        toSmtExpr(c, existentials, sb)
        sb ++= " "
      }
      sb ++= ")"
  }

  def usesEmptyset(a: Specifications.Assertion): Boolean = a.phi.conjuncts.exists(e => e.collect(expr =>
    expr.isInstanceOf[Expressions.SetLiteral] && expr.asInstanceOf[Expressions.SetLiteral].elems.isEmpty).nonEmpty)

  def toSMTTask(goal: Specifications.Goal, grammarExclusion: Option[(Expressions.Var,Expressions.Expr)] = None): String = {
    val sb = new StringBuilder
    sb ++= "(set-logic ALL)\n\n"

    if (goal.gamma.exists { case (v, t) => t == IntSetType && goal.isExistential(v) } || usesEmptyset(goal.post) || usesEmptyset(goal.pre))
      sb ++= s"(define-fun $empsetName () (Set Int) (as emptyset (Set Int)))\n\n"

    if (goal.gamma.exists { case (_, t) => t == IntervalType })
      sb ++= SMTSolving.intervalPrelude.mkString("\n")

    val otherVars = (goal.gamma -- goal.existentials).toList
    for (ex <- goal.existentials) {
      val etypeOpt = ex.getType(goal.gamma)
      val etypeStr = typeToSMT(etypeOpt.get)
      sb ++= "(synth-fun target_" ++= ex.name ++= " ("
      for (v <- otherVars)
        sb ++= "(" ++= v._1.name ++= " " ++= typeToSMT(v._2) ++= ") "
      sb ++= ") " ++= etypeStr ++= "\n"
      sb ++= "  ((Start " ++= etypeStr ++= " ("
      val allRHSs = mutable.ListBuffer.empty[Expressions.Expr]
      for (c <- typeConstants(etypeOpt.get))
        allRHSs += c
      for (v <- otherVars; if v._2.conformsTo(etypeOpt) && (!goal.isProgramLevelExistential(ex) || goal.isProgramVar(v._1))) {
        allRHSs += v._1
        if (goal.env.config.extendedPure) {
          for (u <- typeUnaries(etypeOpt.get)) {
            allRHSs += u(v._1)
          }
        }
      }
      val notExcluded = allRHSs.filter(e => !grammarExclusion.exists(a => ex == a._1 && e == a._2))
      for (e <- notExcluded) {
        toSmtExpr(e, existentialMap, sb)
        sb ++= " "
      }

      sb ++= ")))"
      sb ++= ")\n"
    }
    sb ++= "\n"
    for (v <- otherVars)
      sb ++= "(declare-var " ++= v._1.name ++= " " ++= typeToSMT(v._2) ++= ")\n"
    sb ++= "\n(constraint\n"
    sb ++= "    (=> "
    lazy val existentialMap = mkExistentialCalls(goal.existentials, otherVars)
    toSmt(goal.pre.phi, Map.empty, sb) //no existential vars in pre
    sb ++= " "
    toSmt(goal.post.phi, existentialMap, sb)
    sb ++= "))"
    sb ++= "\n(check-synth)"
    sb.toString
  }

  val cvc4exe = "cvc4"
  val cvc4Cmd = cvc4exe + " --sygus-out=status-or-def --lang sygus" //" --cegqi-si=all --sygus-out=status-or-def --lang sygus"
  def invokeCVC(task: String): Option[String] = { //<-- if we ever get the library compiled, fix it here
    var out: String = null
    val io = BasicIO.standard { ostream =>
      ostream.write(task.getBytes)
      ostream.flush();
      ostream.close()
    }.withOutput { istream =>
      out = scala.io.Source.fromInputStream(istream).mkString
    }
    val cvc4 = cvc4Cmd.run(io)
    if (cvc4.exitValue() != 0) None
    else if (out.trim == "unknown") None //unsynthesizable
    else Some(out)
  }

  private var configured = false

  def isConfigured(): Boolean = this.synchronized {
    configured = try {
      cvc4Cmd.! == 0
    } catch {
      case _: Throwable => false
    }
    configured
  }


  val parser = SMTLIB2Parser[GetModelResponses]

  def parseTerm(term: SMTLIB2Syntax.Term): Expressions.Expr = term match {
    case QIdTerm(SimpleQId(SymbolId(SSymbol(simpleSymbol)))) =>
      if (simpleSymbol == empsetName) Expressions.SetLiteral(List())
      else Expressions.Var(simpleSymbol)
    case ConstantTerm(NumLit(numeralLiteral)) => IntConst(numeralLiteral.toInt)
    case PlusTerm(t1, t2) => t2.foldRight(parseTerm(t1)) {case (t, e) => BinaryExpr(Expressions.OpPlus, e, parseTerm(t))}
    case t => throw SynthesisException(s"Not supported: ${t.getClass.getName}")
  }

  def parseAssignments(cvc4Res: String, gamma: Gamma = Map.empty): Subst = {
    //〈FunDefCmd〉::=  (define-fun〈Symbol〉((〈Symbol〉 〈SortExpr〉)∗)〈SortExpr〉 〈Term〉
    parser.apply(StringSource("(model " + cvc4Res + ")")) match {
      case Failure(exception) => Map.empty
      case Success(GetModelFunDefResponseSuccess(responses)) =>
        responses.map { response =>
          val existential = response.funDef.sMTLIB2Symbol.asInstanceOf[SSymbol].simpleSymbol.drop(7)
          val expr = parseTerm(response.funDef.term) match {
            case e@IntConst(v) => gamma.get(Expressions.Var(existential)) match {
              case Some(LocType) => LocConst(v)
              case _ => e
            }
            case e => e
          }
          Expressions.Var(existential) -> expr
        }.toMap
      case Success(e) => throw SynthesisException(s"Not supported (${e.getClass.getName})")
    }
  }

  def hasSecondResult(goal:Goal, assignment: Subst): Boolean = {
    for (a <- assignment) {
      val newSmtTask = toSMTTask(goal,Some(a))
      val newRes = invokeCVC(newSmtTask)
      if (newRes.isDefined) return true
    }
    false
  }


  abstract class PureSynthesis(val isFinal: Boolean) extends SynthesisRule with RuleUtils {
    val exceptionQualifier: String = "rule-pure-synthesis"

    def apply(goal: Goal): Seq[RuleResult] = {
      if (!goal.env.config.delegatePure || !configured) return Nil
      if (goal.existentials.isEmpty) return Nil

      val smtTask = toSMTTask(goal)
      val cvc4Res = invokeCVC(smtTask)
      if (cvc4Res.isEmpty) {
        if (goal.env.config.branchAbduction) UnificationRules.Pick(goal)
        else List(RuleResult(List(goal.unsolvableChild), IdProducer, this, goal))
      }
      else {
        //parse me
        val assignments: Subst = parseAssignments(cvc4Res.get, goal.gamma)
        val newPost = goal.post.subst(assignments)
        val newCallGoal = goal.callGoal.map(_.updateSubstitution(assignments))
        val newGoal = goal.spawnChild(post = newPost, callGoal = newCallGoal)
        if (isFinal || !DelegatePureSynthesis.hasSecondResult(goal,assignments)) {
          val kont = SubstMapProducer(assignments) >> IdProducer >> ExtractHelper(goal)
          val alternatives = RuleResult(List(newGoal), kont, this, goal) :: Nil
          nubBy[RuleResult, Assertion](alternatives, res => res.subgoals.head.post)
        }
        else UnificationRules.Pick(goal)
      }
    }
  }

  object PureSynthesisFinal extends PureSynthesis(true) with InvertibleRule {
    override def toString: String = "PureSynthesisFinal"
  }

  object PureSynthesisNonfinal extends PureSynthesis(false) {
    override def toString: String = "PureSynthesisNonFinal"
  }

}
