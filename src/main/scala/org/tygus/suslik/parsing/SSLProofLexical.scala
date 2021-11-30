package org.tygus.suslik.parsing

import scala.util.parsing.combinator.lexical.StdLexical

/**
  * @author Ilya Sergey
  */
class SSLProofLexical extends SSLLexical {

  // Add tactics
  reserved += ("Emp", "HaltAndPrintGoal", "StarPartial", "NilNotLval", "Read", "Frame",
    "SubstL", "SubstR", "Write", "CheckPost"
  )

  delimiters += ("->")


}
