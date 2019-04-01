package org.tygus.suslik.parsing

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.unification.UnificationGoal
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.synthesis.SynthesisException

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer

class SSLParser extends StandardTokenParsers with SepLogicUtils {

  // Modified repN
  def repAll[T](p: => Parser[T]): Parser[List[T]] =
    Parser { in =>
      val elems = new ListBuffer[T]
      val p0 = p    // avoid repeatedly re-evaluating by-name parser

      @tailrec def applyp(in0: Input): ParseResult[List[T]] =
        if (in0.atEnd) Success(elems.toList, in0)
        else p0(in0) match {
          case Success(x, rest) => elems += x ; applyp(rest)
          case ns: NoSuccess    => ns
        }

      applyp(in)
    }

  override val lexical = new SSLLexical

  def typeParser: Parser[SSLType] =
    ("int" ^^^ IntType
        | "bool" ^^^ BoolType
        | "loc" ^^^ LocType
        | "set" ^^^ IntSetType
        | "void" ^^^ VoidType)

  def formal: Parser[(SSLType, Var)] = typeParser ~ ident ^^ { case a ~ b => (a, Var(b)) }

  def intLiteral: Parser[Const] =
    numericLit ^^ (x => IntConst(Integer.parseInt(x)))

  def boolLiteral: Parser[Const] =
    ("true" | "false") ^^ (b => BoolConst(java.lang.Boolean.parseBoolean(b)))

  def setLiteral: Parser[Expr] =
    "{" ~> repsep(expr, ",") <~ "}" ^^ SetLiteral

  def varParser: Parser[Var] = ident ^^ Var

  def unOpParser: Parser[UnOp] =
    "not" ^^^ OpNot ||| "-" ^^^ OpUnaryMinus

  // TODO: remove legacy ++, --, =i, /\, \/, <=i
  def termOpParser: Parser[OverloadedBinOp] = (
    ("++" ||| "+") ^^^ OpOverloadedPlus
      ||| ("--" ||| "-") ^^^ OpOverloadedMinus
      ||| "*" ^^^ OpOverloadedStar
    )

  def relOpParser: Parser[OverloadedBinOp] = (
    "<" ^^^ OpLt
      ||| ">" ^^^ OpGt
      ||| ">=" ^^^ OpGeq
      ||| "!=" ^^^ OpNotEqual
      ||| ("==" | "=i") ^^^ OpOverloadedEq
      ||| ("<=" ||| "<=i") ^^^ OpOverloadedLeq
      ||| "in" ^^^ OpIn
    )

  def logOpParser: Parser[OverloadedBinOp] = (
    ("\\/" | "||") ^^^ OpOr
      ||| ("/\\" | "&&") ^^^ OpAnd
      ||| "==>" ^^^ OpImplication
    )

  def binOpParser(p: Parser[OverloadedBinOp]): Parser[(Expr, Expr) => Expr] = {
    p ^^ { op => (l, r) => OverloadedBinaryExpr(op, l, r) }
  }

  def atom: Parser[Expr] = (
      unOpParser ~ atom ^^ { case op ~ a => UnaryExpr(op, a) }
          | "(" ~> expr <~ ")"
          | intLiteral | boolLiteral | setLiteral
          | varParser
      )

  def term: Parser[Expr] = chainl1(atom, binOpParser(termOpParser))

  def relExpr: Parser[Expr] =
    term ~ opt(relOpParser ~ term) ^^ {
      case a ~ None => a
      case a ~ Some(op ~ b) => OverloadedBinaryExpr(op, a, b)
    }

  def expr: Parser[Expr] =
    chainl1(relExpr, binOpParser(logOpParser)) ~ opt(("?" ~> expr <~ ":") ~ expr) ^^ {
      case a ~ None => a
      case a ~ Some(l ~ r) => IfThenElse(a, l, r)
    }

  def identWithOffset: Parser[(Ident, Int)] = {
    val ov = ident ~ opt("+" ~> numericLit)
    ("(" ~> ov <~ ")" | ov) ^^ { case i ~ o =>
      val off = Math.max(Integer.parseInt(o.getOrElse("0")), 0)
      (i, off)
    }
  }

  def heaplet: Parser[Heaplet] = (
      (identWithOffset <~ ":->") ~ expr ^^ { case (a, o) ~ b => PointsTo(Var(a), o, b) }
          ||| "[" ~> (ident ~ ("," ~> numericLit)) <~ "]" ^^ { case a ~ s => Block(Var(a), Integer.parseInt(s)) }
          ||| ident ~ ("(" ~> rep1sep(expr, ",") <~ ")") ^^ { case name ~ args => SApp(name, args) }
      )

  def sigma: Parser[SFormula] = (
      "emp" ^^^ SFormula(Nil)
          ||| repsep(heaplet, "**") ^^ { hs => SFormula(hs) }
      )

  def assertion: Parser[Assertion] = "{" ~> (opt(expr <~ ";") ~ sigma) <~ "}" ^^ {
    case Some(p) ~ s => Assertion(desugar(p), s)
    case None ~ s => Assertion(pTrue, s)
  }

  def indClause: Parser[InductiveClause] =
    expr ~ ("=>" ~> assertion) ^^ { case p ~ a => InductiveClause(p, a) }

  def indPredicate: Parser[InductivePredicate] =
    ("predicate" ~> ident) ~ ("(" ~> repsep(formal, ",") <~ ")") ~
        (("{" ~ opt("|")) ~> rep1sep(indClause, "|") <~ "}") ^^ {
      case name ~ formals ~ clauses => InductivePredicate(name, formals, clauses)
    }

  def uGoal: Parser[UnificationGoal] = ("(" ~> rep1sep(varParser, ",") <~ ")") ~ assertion ^^ {
    case params ~ formula => UnificationGoal(formula, params.toSet)
  }

  def varsDeclaration: Parser[Formals] = "[" ~> repsep(formal, ",") <~ "]"

  def goalFunctionSYN: Parser[FunSpec] = assertion ~ typeParser ~ ident ~ ("(" ~> repsep(formal, ",") <~ ")") ~ varsDeclaration.? ~ assertion ^^ {
    case pre ~ tpe ~ name ~ formals ~ vars_decl ~ post => FunSpec(name, tpe, formals, pre, post, vars_decl.getOrElse(Nil))
  }

  def nonGoalFunction: Parser[FunSpec] =  typeParser ~ ident ~ ("(" ~> repsep(formal, ",") <~ ")") ~ varsDeclaration.? ~ assertion ~ assertion ^^ {
    case  tpe ~ name ~ formals  ~ vars_decl ~ pre ~ post => FunSpec(name, tpe, formals, pre, post, vars_decl.getOrElse(Nil))
  }

  def statementParser:Parser[Statement] = (
    ("??" ^^^ Hole)
      ||| ("error" ~> ";" ^^^ Statements.Error)
      ||| ("magic" ~> ";" ^^^ Magic)
      // Malloc
      ||| "let" ~> varParser ~ ("=" ~> "malloc" ~> "(" ~> numericLit <~ ")" ~> ";") ^^ {
        case variable ~ number_str => Malloc(variable, IntType, Integer.parseInt(number_str)) // todo: maybe not ignore type here
      }
      ||| ("free" ~> "(" ~> varParser <~ ")" ~> ";") ^^ Free
      // Store
      ||| "*" ~> varParser ~ ("=" ~> expr <~ ";") ^^ {
        case variable ~ e => Store(variable, 0, e)
      }
      ||| ("*" ~> "(" ~> varParser <~ "+") ~ numericLit ~ (")" ~> "=" ~> expr <~ ";") ^^ {
        case variable ~ offset_str ~ e => Store(variable, Integer.parseInt(offset_str), e)
      }
      // Load
      ||| ("let" ~> varParser) ~ ("=" ~> "*" ~> varParser <~ ";") ^^ {
        case to ~ from => Load(to, IntType, from) // todo: maybe not ignore type here
      }
      ||| ("let" ~> varParser <~ "=" <~ "*" <~ "(") ~ (varParser <~ "+") ~ (numericLit <~ ")" <~ ";") ^^ {
        case to ~ from ~ offset_str => Load(to, IntType, from, Integer.parseInt(offset_str)) // todo: maybe not ignore type here
      }
      // Call
      ||| varParser ~ ("(" ~> repsep(expr, ",") <~ ")" <~ ";") ^^ {
        case fun ~ args => Call(None, fun, args)
      }
      ||| typeParser ~ (varParser <~ "=") ~ varParser ~ ("(" ~> repsep(expr, ",") <~ ")" <~ ";") ^^ {
        case tpe ~ to ~ fun ~ args => Call(Some((to, tpe)), fun, args)
      }
      // if
      ||| ("if" ~> "(" ~> expr <~ ")") ~ ("{" ~> codeWithHoles <~ "}") ~ ("else" ~> "{" ~> codeWithHoles <~ "}") ^^ {
        case cond ~ tb ~ eb => If(cond, tb, eb)
      }
      // Guarded
      ||| ("assume" ~> "(" ~> expr <~ ")") ~ ("{" ~> codeWithHoles <~ "}")  ^^ {
        case cond ~ body => Guarded(cond, body)
      }
    )

  def codeWithHoles:Parser[Statement] = rep(statementParser) ^^ (seq => if(seq.nonEmpty) seq.reduceLeft(SeqComp) else Skip)

  case class GoalContainer(goal: FunSpec) // just to distinguish from FunSpec while matching in `program`
  def goalFunctionV1: Parser[GoalContainer] =  nonGoalFunction <~ "{" <~ codeWithHoles <~ "}" ^^ GoalContainer

  def programSUS: Parser[Program] = repAll(indPredicate | (goalFunctionV1 ||| nonGoalFunction)) ^^ { pfs =>
    val ps = for (p@InductivePredicate(_, _, _) <- pfs) yield p
    val fs = for (f@FunSpec(_, _, _, _, _, _) <- pfs) yield f
    val goals = for (GoalContainer(g) <- pfs) yield g
    if (goals.isEmpty) {
      throw SynthesisException("Parsing failed: no single goal spec is provided.")
    }
    if (goals.size > 1) {
      throw SynthesisException("Parsing failed: more than one goal is provided.")
    }
    val goal = goals.last
    Program(ps, fs, goal)
  }

  def programSYN: Parser[Program] = repAll(indPredicate | goalFunctionSYN) ^^ { pfs =>
    val ps = for (p@InductivePredicate(_, _, _) <- pfs) yield p
    val fs = for (f@FunSpec(_, _, _, _, _, _) <- pfs) yield f
    if (fs.isEmpty){
      throw SynthesisException("Parsing failed. No single function spec is provided.")
    }
    val goal = fs.last
    val funs = fs.take(fs.length - 1)
    Program(ps, funs, goal)
  }

  def parse[T](p: Parser[T])(input: String): ParseResult[T] = p(new lexical.Scanner(input)) match {
    case e: Error => Failure(e.msg, e.next)
    case Success(_, in) if !in.atEnd => Failure("Not fully parsed", in)
    case s => s
  }

  def parseUnificationGoal(input: String): ParseResult[UnificationGoal] = parse(uGoal)(input)

  def parseGoalSYN(input: String): ParseResult[Program] = parse(programSYN)(input)
  def parseGoalSUS(input: String): ParseResult[Program] = parse(programSUS)(input)
  def parseGoal = parseGoalSYN _
}
