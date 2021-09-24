package org.tygus.suslik.certification

import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.language.Expressions.{BinOp, Expr, OverloadedBinOp, Subst, UnOp, Var}
import org.tygus.suslik.language.{Ident, SSLType}
import org.tygus.suslik.language.Statements.{Call, Free, Hole, Load, Malloc, Statement, Store}
import org.tygus.suslik.logic.{Environment, FunSpec, FunctionEnv, Gamma, Heaplet, InductiveClause, InductivePredicate, PFormula, PTag, PredicateEnv, SApp, SFormula}
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
  implicit val varFormat : RootJsonFormat[Var] = jsonFormat[Var]

  val var_as_string_Format : RootJsonFormat[Var] = new RootJsonFormat[Var] {
    override def write(obj: Var): JsValue = JsString(obj.name)

    override def read(json: JsValue): Var = json match {
      case JsString(value) => Var(value)
    }
  }

  implicit val exprPairFormat : RootJsonFormat[(Expr,Expr)] = new RootJsonFormat[(Expr, Expr)] {
    override def read(json: JsValue): (Expr, Expr) =
      json.convertTo(listFormat(exprFormat)) match {
          case ::(fst, ::(snd, Nil)) => (fst,snd)
      }

    override def write(obj: (Expr, Expr)): JsValue =
    obj match {
      case (fst,snd) => List(fst,snd).toJson(listFormat(exprFormat))
    }

  }
  implicit val exprMapFormat : RootJsonFormat[Map[Expr,Expr]] = new RootJsonFormat[Map[Expr,Expr]] {
    override def write(obj: Map[Expr,Expr]): JsValue = obj.toList.toJson(listFormat(exprPairFormat))
    override def read(json: JsValue): Map[Expr,Expr] = {
      json.convertTo(listFormat(exprPairFormat)).toMap
    }
  }


  implicit val varMapFormat : RootJsonFormat[Map[Var,Var]] = new RootJsonFormat[Map[Var,Var]] {
    override def write(obj: Map[Var,Var]): JsValue = obj.toJson(mapFormat(var_as_string_Format,var_as_string_Format))
    override def read(json: JsValue): Map[Var,Var] = json.convertTo(mapFormat(var_as_string_Format,var_as_string_Format))
  }


  implicit val substFormat : RootJsonFormat[Map[Var,Expr]] = new RootJsonFormat[Map[Var,Expr]] {
    override def write(obj: Map[Var,Expr]): JsValue = obj.toJson(mapFormat(var_as_string_Format,exprFormat))
    override def read(json: JsValue): Map[Var,Expr] = json.convertTo(mapFormat(var_as_string_Format,exprFormat))
  }

  implicit val typEnvFormat : RootJsonFormat[Map[Var, SSLType]] = new RootJsonFormat[Map[Var, SSLType]] {
    override def write(obj: Map[Var, SSLType]): JsValue = obj.toJson(mapFormat(var_as_string_Format, tyFormat))
    override def read(json: JsValue): Map[Var, SSLType] =json.convertTo(mapFormat(var_as_string_Format, tyFormat))
  }

  implicit val clauseFormat : RootJsonFormat[InductiveClause] = jsonFormat[InductiveClause]
  implicit val predFormat : RootJsonFormat[InductivePredicate] = jsonFormat[InductivePredicate]
  implicit val exprFormat: RootJsonFormat[Expr] = jsonFormat[Expr]
  implicit val goalFormat : RootJsonFormat[Goal] = new RootJsonFormat[Goal] {
    object JSONGoal {

      case class Goal(pre: Assertion,
                      post: Assertion,
                      gamma: Gamma, // types of all variables (program, universal, and existential)
                      programVars: List[Var], // program-level variables
                      universalGhosts: Set[Var], // universally quantified ghost variables
                      fname: String, // top-level function name
                      label: GoalLabel, // unique id within the derivation
                      parent: Option[Goal], // parent goal in the derivation
                      predicates: Map[String, InductivePredicate],
                      functions: Map[String,FunSpec]
                     )

      implicit val goalFormat: RootJsonFormat[Goal] = jsonFormat[Goal]
    }

    def of_goal(obj: Goal) : JSONGoal.Goal =
      JSONGoal.Goal(
        obj.pre, obj.post, obj.gamma,
        obj.programVars, obj.universalGhosts, obj.fname,
        obj.label, obj.parent.map(of_goal),
        obj.env.predicates, obj.env.functions)
    def to_goal(obj: JSONGoal.Goal) : Goal =
      Goal(
        obj.pre, obj.post, obj.gamma,
        obj.programVars, obj.universalGhosts, obj.fname,
        obj.label, obj.parent.map(to_goal),
        Environment(obj.predicates, obj.functions, SynConfig(), new SynStats(0)),
        Hole, None, false, false
      )


    override def write(obj: Goal): JsValue = of_goal(obj).toJson

    override def read(json: JsValue): Goal = {
      val goal = json.convertTo(JSONGoal.goalFormat)
      to_goal(goal)
    }
  }
  implicit val proofStepFormat: RootJsonFormat[SuslikProofStep] = jsonFormat[SuslikProofStep]
  implicit val proofTreeFormat: RootJsonFormat[ProofTree[SuslikProofStep]] = jsonFormat[ProofTree[SuslikProofStep]]

}
