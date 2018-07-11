package org.tygus.suslik.parsing

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.util.SynLogLevels

/**
  * @author Ilya Sergey
  */

class PreambleParserTests extends FunSpec with Matchers {

  val log = SynLogLevels.Test
  import log._

  val pred1 =
    """predicate lseg (loc x, loc y) {
      | x == y  =>  {emp}
      | not (x == y)  => {x :-> v ** x + 1 :-> z ** lseg(z, y)}
      }

      {emp} void foo (loc x) {emp}
    """

  def parseSimpleSpec(text: String) {
    val parser = new SSLParser
    val result = parser.parseGoal(text)
    // So far, just assert that the result is a success
    assert(result.successful, result)
    val res = result.get
//    assert(res.nonEmpty)
//    println(res.head)
    println(res.pp)
  }

  describe("Parser for SSL definitions") {
    it("should parse a list predicate") {
      parseSimpleSpec(pred1)
    }
  }


}

