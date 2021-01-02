package org.tygus.suslik.logic.smt

import org.bitbucket.franck44.scalasmt.configurations.SMTInit
import org.bitbucket.franck44.scalasmt.interpreters.{Resources, SMTSolver}
import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax._
import org.bitbucket.franck44.scalasmt.theories._
import org.bitbucket.franck44.scalasmt.typedterms.{Commands, QuantifiedTerm, TypedTerm, VarTerm}
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic._
import org.tygus.suslik.report.LazyTiming

import scala.util.Success

/**
  * @author Ilya Sergey
  */

object SMTSolving extends Core
  with IntegerArithmetics
  with QuantifiedTerm
  with Resources
  with Commands
  with PureLogicUtils
  with ArrayExBool
  with ArrayExOperators
  with LazyTiming {

  val defaultSolver = "Z3" // other choices: "Z3 <= 4.7.x", "CVC4"

  override val watchName = "SMTSolving"

  implicit private var solverObject: SMTSolver = null

  {
    disableLogging()

    // create solver and assert axioms
    // TODO: destroy solver when we're done
    solverObject = new SMTSolver(defaultSolver, new SMTInit())
    for (cmd <- prelude) {
      solverObject.eval(Raw(cmd))
    }

    // Warm-up the SMT solver on start-up to avoid future delays
    for (i <- 1 to 5; j <- 1 to 2; k <- 1 to 3) {
      checkSat(convertBoolExpr(BinaryExpr(OpLeq, IntConst(i), BinaryExpr(OpPlus, IntConst(j), IntConst(k)))))
    }
  }

  /** Communication with the solver  */

  trait SetTerm

  type SMTBoolTerm = TypedTerm[BoolTerm, Term]
  type SMTIntTerm = TypedTerm[IntTerm, Term]
  //  type SMTSetTerm = TypedTerm[ArrayTerm[BoolTerm], Term]
  type SMTSetTerm = TypedTerm[SetTerm, Term]

  def setSort: Sort = SortId(SymbolId(SSymbol("SetInt")))

  def emptySetSymbol = SimpleQId(SymbolId(SSymbol("empty")))

  def setInsertSymbol = SimpleQId(SymbolId(SSymbol("insert")))

  def setUnionSymbol = SimpleQId(SymbolId(SSymbol("union")))

  def setDiffSymbol = SimpleQId(SymbolId(SSymbol("difference")))

  def setMemberSymbol = SimpleQId(SymbolId(SSymbol("member")))

  def setSubsetSymbol = SimpleQId(SymbolId(SSymbol("subset")))

  def setIntersectSymbol = SimpleQId(SymbolId(SSymbol("intersect")))

  def emptySetTerm: Term = QIdTerm(emptySetSymbol)

  // Commands to be executed before solving starts
  def prelude = if (defaultSolver == "CVC4") {
    List(
      "(set-logic ALL_SUPPORTED)",
      "(define-sort SetInt () (Set Int))",
      "(define-fun empty () SetInt (as emptyset (Set Int)))")
  } else if (defaultSolver == "Z3") {
    List(
      "(define-sort SetInt () (Array Int Bool))",
      "(define-fun empty () SetInt ((as const SetInt) false))",
      "(define-fun member ((x Int) (s SetInt)) Bool (select s x))",
      "(define-fun insert ((x Int) (s SetInt)) SetInt (store s x true))",
      "(define-fun intersect ((s1 SetInt) (s2 SetInt)) SetInt (intersection s1 s2))",
      "(define-fun subset ((s1 SetInt) (s2 SetInt)) Bool (= s1 (intersect s1 s2)))",
      "(declare-fun andNot (Bool Bool) Bool)",
      "(assert (forall ((b1 Bool) (b2 Bool)) (= (andNot b1 b2) (and b1 (not b2)))))",
      "(define-fun difference ((s1 SetInt) (s2 SetInt)) SetInt ((_ map andNot) s1 s2))")
  } else if (defaultSolver == "Z3 <= 4.7.x") {
    // In Z3 4.7.x and below, difference is built in and intersection is called intersect
    List(
      "(define-sort SetInt () (Array Int Bool))",
      "(define-fun empty () SetInt ((as const SetInt) false))",
      "(define-fun member ((x Int) (s SetInt)) Bool (select s x))",
      "(define-fun insert ((x Int) (s SetInt)) SetInt (store s x true))")
//      "(define-fun union ((s1 SetInt) (s2 SetInt)) SetInt (((_ map or) s1 s2)))",
  } else throw SolverUnsupportedExpr(defaultSolver)

  private def checkSat(term: SMTBoolTerm): Boolean =
    this.synchronized {
      timed {
        push(1)
        val res = isSat(term)
        pop(1)
        res != Success(UnSat()) // Unknown counts as SAT
      }
    }

  /** Translating expression into SMT  */

  case class SMTUnsupportedExpr(e: Expr)
    extends Exception(s"Cannot convert expression ${e.pp} to an equivalent SMT representation.")

  case class SolverUnsupportedExpr(solver: String)
    extends Exception(s"Unsupported solver: $solver.")

  private def convertSetExpr(e: Expr): SMTSetTerm = e match {
    case Var(name) => new VarTerm[SetTerm](name, setSort)
    case SetLiteral(elems) => {
      val emptyTerm = new TypedTerm[SetTerm, Term](Set.empty, emptySetTerm)
      makeSetInsert(emptyTerm, elems)
    }
    // Special case for unions with a literal
    case BinaryExpr(OpUnion, SetLiteral(elems1), SetLiteral(elems2)) => {
      val emptyTerm = new TypedTerm[SetTerm, Term](Set.empty, emptySetTerm)
      makeSetInsert(emptyTerm, elems1 ++ elems2)
    }
    case BinaryExpr(OpUnion, left, SetLiteral(elems)) => {
      val l = convertSetExpr(left)
      makeSetInsert(l, elems)
    }
    case BinaryExpr(OpUnion, SetLiteral(elems), right) => {
      val r = convertSetExpr(right)
      makeSetInsert(r, elems)
    }
    case BinaryExpr(OpUnion, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      new TypedTerm[SetTerm, Term](l.typeDefs ++ r.typeDefs, QIdAndTermsTerm(setUnionSymbol, List(l.termDef, r.termDef)))
    }
    case BinaryExpr(OpDiff, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      new TypedTerm[SetTerm, Term](l.typeDefs ++ r.typeDefs, QIdAndTermsTerm(setDiffSymbol, List(l.termDef, r.termDef)))
    }
    case BinaryExpr(OpIntersect, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      new TypedTerm[SetTerm, Term](l.typeDefs ++ r.typeDefs, QIdAndTermsTerm(setIntersectSymbol, List(l.termDef, r.termDef)))
    }
    case _ => throw SMTUnsupportedExpr(e)
  }

  private def makeSetInsert(setTerm: SMTSetTerm, elems: List[Expr]): SMTSetTerm = {
    if (elems.isEmpty) {
      setTerm
    } else {
      val eTerms: List[SMTIntTerm] = elems.map(convertIntExpr)
      if (defaultSolver == "CVC4") {
        new TypedTerm[SetTerm, Term](setTerm.typeDefs ++ eTerms.flatMap(_.typeDefs).toSet,
          QIdAndTermsTerm(setInsertSymbol, (eTerms :+ setTerm).map(_.termDef)))
      } else if (defaultSolver == "Z3" || defaultSolver == "Z3 <= 4.7.x") {
        def makeInsertOne(setTerm: SMTSetTerm, eTerm: SMTIntTerm): SMTSetTerm =
          new TypedTerm[SetTerm, Term](setTerm.typeDefs ++ eTerm.typeDefs,
            QIdAndTermsTerm(setInsertSymbol, List(eTerm.termDef, setTerm.termDef)))

        eTerms.foldLeft(setTerm)(makeInsertOne)
      } else throw SolverUnsupportedExpr(defaultSolver)
    }
  }

  private def convertBoolExpr(e: Expr): SMTBoolTerm = e match {
    case Var(name) => Bools(name)
    case BoolConst(true) => True()
    case BoolConst(false) => False()
    case UnaryExpr(OpNot, e1) => !convertBoolExpr(e1)
    case BinaryExpr(OpAnd, left, right) => {
      val l = convertBoolExpr(left)
      val r = convertBoolExpr(right)
      l & r
    }
    case BinaryExpr(OpOr, left, right) => {
      val l = convertBoolExpr(left)
      val r = convertBoolExpr(right)
      l | r
    }
    case BinaryExpr(OpEq, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      l === r
    }
    case BinaryExpr(OpBoolEq, left, right) => {
      val l = convertBoolExpr(left)
      val r = convertBoolExpr(right)
      l === r
    }
    case BinaryExpr(OpLeq, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      l <= r
    }
    case BinaryExpr(OpLt, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      l < r
    }
    case BinaryExpr(OpIn, left, right) => {
      val l = convertIntExpr(left)
      val r = convertSetExpr(right)
      new TypedTerm[BoolTerm, Term](l.typeDefs ++ r.typeDefs,
        QIdAndTermsTerm(setMemberSymbol, List(l.termDef, r.termDef)))
    }
    case BinaryExpr(OpSetEq, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      l === r
    }
    case BinaryExpr(OpSubset, left, right) => {
      val l = convertSetExpr(left)
      val r = convertSetExpr(right)
      new TypedTerm[BoolTerm, Term](l.typeDefs ++ r.typeDefs,
        QIdAndTermsTerm(setSubsetSymbol, List(l.termDef, r.termDef)))
    }
    case Unknown(_, _, _) => True() // Treat unknown predicates as true
    case _ => throw SMTUnsupportedExpr(e)
  }

  private def convertIntExpr(e: Expr): SMTIntTerm = e match {
    case Var(name) => Ints(name)
    case IntConst(c) => Ints(c)
    case BinaryExpr(op, left, right) => {
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      op match {
        case OpPlus => l + r
        case OpMinus => l - r
        case OpMultiply => l * r
        case _ => throw SMTUnsupportedExpr(e)
      }
    }
    case IfThenElse(cond, left, right) => {
      val c = convertBoolExpr(cond)
      val l = convertIntExpr(left)
      val r = convertIntExpr(right)
      c.ite(l, r)
    }
    case _ => throw SMTUnsupportedExpr(e)
  }

  /** Caching */

  private val cache = collection.mutable.Map[Expr, Boolean]()

  def cacheSize: Int = cache.size

  // Call this before synthesizing a new function
  def init(): Unit = {
    // Warm up solver
    cache.clear()
  }

  /** External interface */

  // Check if phi is satisfiable; all vars are implicitly existentially quantified
  def sat(phi: Expr): Boolean = {
    cache.getOrElseUpdate(phi, checkSat(convertBoolExpr(phi)))
  }

  // Check if phi is valid; all vars are implicitly universally quantified
  def valid(phi: Expr): Boolean = {
    !sat(phi.not)
  }

}
