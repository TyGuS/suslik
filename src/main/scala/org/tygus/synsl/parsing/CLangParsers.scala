package org.tygus.synsl.parsing

import org.tygus.synsl.language.syntax.{CLang, Expressions}

import scala.util.parsing.combinator.syntactical.StandardTokenParsers

/**
  * @author Ilya Sergey
  */

class CLangParsers extends StandardTokenParsers with CLang with Expressions {
  override val lexical = new SynslLexical


}


