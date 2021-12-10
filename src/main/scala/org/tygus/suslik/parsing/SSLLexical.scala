package org.tygus.suslik.parsing

import scala.util.parsing.combinator.lexical.StdLexical

/**
  * @author Ilya Sergey
  */
class SSLLexical extends StdLexical {

  // Add keywords
  reserved += ("if", "then", "else", "true", "false", "emp", "not", "return", "predicate", "in", "lower", "upper")
  reserved += ("error","malloc", "free", "let", "assume")
  reserved += ("null","mut","imm")

  // Types
  reserved += ("int", "bool", "loc", "set", "void", "interval", "perm")

  delimiters += ("(", ")", "=", ";", "**", "*", ":->", "=i", "<=i", "++", "--", "..",
      "{", "}", "/\\", "&&", "\\/", "||", "\n", "\r", "=>", "?", ":",
      "<", ">", ",", "/",   "+", "-", "==", "!=", "==>", "<=", ">=", "[", "]", "|", "??", "@"
  )

}
