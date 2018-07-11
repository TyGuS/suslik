package org.tygus.suslik.parsing

import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.input.CharArrayReader.EofCh

/**
  * @author Ilya Sergey
  */
class SSLLexical extends StdLexical {

  // Add keywords
  reserved += ("if", "then", "else", "true", "false", "emp", "not", "return", "predicate", "in")

  // Types
  reserved += ("int", "bool", "loc", "set", "void")

  delimiters += ("(", ")", "=", ";", "**", "*", ":->", "=i", "++",
      "{", "}", "/\\", "\\/", "\n", "\r", "=>", "?", ":",
      "<", ",", "/",   "+", "-", "==", "<=", "[", "]", "|"
  )

  // see `whitespace in `Scanners`
  override def whitespace: Parser[Any] = rep[Any](
    whitespaceChar
        | '/' ~ '*' ~ comment
        | '/' ~ '*' ~ failure("unclosed comment")
  )

  override protected def comment: Parser[Any] = (
      rep(chrExcept(EofCh, '*')) ~ '*' ~ '/' ^^ (_ => ' ')
          | rep(chrExcept(EofCh, '*')) ~ '*' ~ comment ^^ (_ => ' ')
      )

}
