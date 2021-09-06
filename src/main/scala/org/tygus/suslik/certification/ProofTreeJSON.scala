package org.tygus.suslik.certification

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.language.Expressions.{BinOp, Expr, OverloadedBinOp, UnOp, Var}
import org.tygus.suslik.language.SSLType
import org.tygus.suslik.language.Statements.{Call, Free, Hole, Load, Malloc, Statement, Store}
import org.tygus.suslik.logic.{Environment, FunSpec, Heaplet, PFormula, PTag, PredicateEnv, SApp, SFormula}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal, GoalLabel, SuspendedCallGoal}
import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.util.SynStats
import spray.json.{DefaultJsonProtocol, DerivedFormats, JsArray, JsBoolean, JsNull, JsNumber, JsObject, JsString, JsValue, RootJsonFormat, enrichAny}
import upickle.default.{macroRW, ReadWriter => RW}

import scala.collection.immutable.SortedSet

object ProofTreeJSON extends DefaultJsonProtocol with DerivedFormats {
  implicit val integerFormat : RootJsonFormat[Integer] = new RootJsonFormat[Integer] {
    override def write(obj: Integer): JsValue = {
      new JsObject(Map(
        ("@type", JsString("Integer")),
        ("value", JsNumber(obj.toInt))
      ))
    }

    override def read(json: JsValue): Integer = {
      val fields = json.asJsObject().getFields("@type", "value")
      fields match {
        case (JsString("Integer") :: JsNumber(value) :: _) => Integer.valueOf(value.toInt)
      }
    }
  }
  implicit val tyFormat : RootJsonFormat[SSLType] = jsonFormat[SSLType]
  implicit val unaryOpFormat : RootJsonFormat[UnOp] = jsonFormat[UnOp]
  implicit val binOpFormat : RootJsonFormat[BinOp] = jsonFormat[BinOp]
  implicit val overloadedBinOpFormat : RootJsonFormat[OverloadedBinOp] = jsonFormat[OverloadedBinOp]
  implicit val goalLabelFormat : RootJsonFormat[GoalLabel] = jsonFormat[GoalLabel]
  implicit val storeFormat : RootJsonFormat[Store] = jsonFormat[Store]
  implicit val sappFormat : RootJsonFormat[SApp] = jsonFormat[SApp]
  implicit val pTagFormat : RootJsonFormat[PTag] = jsonFormat[PTag]

  implicit val ssexprFormat : RootJsonFormat[SortedSet[Expr]] = new RootJsonFormat[SortedSet[Expr]] {
    override def write(obj: SortedSet[Expr]): JsValue =
      new JsObject(
        Map(("elts", obj.toList.toJson))
      )
    override def read(json: JsValue): SortedSet[Expr] = {
      val elts = json.asJsObject().getFields("elts").head
      SortedSet[Expr]() ++ (elts.fromJson(listFormat(exprFormat)))
    }
  }

  implicit val pFormulaFormat : RootJsonFormat[PFormula] = jsonFormat[PFormula]
  implicit val loadFormat : RootJsonFormat[Load] = jsonFormat[Load]
  implicit val mallocFormat : RootJsonFormat[Malloc] = jsonFormat[Malloc]
  implicit val freeFormat : RootJsonFormat[Free] = jsonFormat[Free]
  implicit val callFormat : RootJsonFormat[Call] = jsonFormat[Call]
  implicit val assertionFormat : RootJsonFormat[Assertion] = jsonFormat[Assertion]
  implicit val sformulaFormat : RootJsonFormat[SFormula] = jsonFormat[SFormula]
  implicit val heapletFormat : RootJsonFormat[Heaplet] = jsonFormat[Heaplet]
  implicit val funspecFormat : RootJsonFormat[FunSpec] = jsonFormat[FunSpec]
  // implicit val goalFormat : RootJsonFormat[Goal] = jsonFormat[Goal]
  // implicit val suspendedCallGoalFormat : RootJsonFormat[SuspendedCallGoal] = jsonFormat[SuspendedCallGoal]
  // implicit val envFormat : RootJsonFormat[Environment] = jsonFormat[Environment]
  // implicit val predicateEnvFormat : RootJsonFormat[PredicateEnv] = jsonFormat[PredicateEnv]
  implicit val stmtFormat : RootJsonFormat[Statement] = jsonFormat[Statement]
  implicit val varFormat : RootJsonFormat[Var] = new RootJsonFormat[Var] {
    override def write(obj: Var): JsValue = JsString(obj.name)

    override def read(json: JsValue): Var = json match {
      case JsString(value) => Var(value)
    }
  }
  implicit val exprFormat: RootJsonFormat[Expr] = jsonFormat[Expr]
  implicit val goalFormat : RootJsonFormat[Goal] = new RootJsonFormat[Goal] {
    override def write(obj: Goal): JsValue = new JsObject(Map(
      ("@type", JsString("goal")),
      ("value", JsString("<goal>")
      )))

    override def read(json: JsValue): Goal = {
      val emp_assert = Assertion(new PFormula(SortedSet()), new SFormula(List()))
      Goal(emp_assert, emp_assert, Map(), List(), Set(), "", GoalLabel(List(),List()),
        None, Environment(Map(), Map(), SynConfig(), new SynStats(0)), Hole, None, false, false)
    }
  }
  implicit val proofStepFormat: RootJsonFormat[SuslikProofStep] = jsonFormat[SuslikProofStep]
  implicit val proofTreeFormat: RootJsonFormat[ProofTree[SuslikProofStep]] = jsonFormat[ProofTree[SuslikProofStep]]

}
