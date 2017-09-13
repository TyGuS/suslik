package org.tygus.synsl.parsing

import org.scalatest.{FunSpec, Matchers}

/**
  * @author Ilya Sergey
  */

class PreambleParserTests extends FunSpec with Matchers {

  val pred1 =
    """lseg(x, y) {
      | x == y  =>  emp
      | not (x == y)  => x :-> v ** x + 1 :-> z ** lseg(z, y)
      }
    """

  def parseSimpleSpec(text: String) {
    val parser = new SynslParser
    val result = parser.parsePreamble(text)
    // So far, just assert that the result is a success
    assert(result.successful, result)
    val res = result.get
//    assert(res.nonEmpty)
//    println(res.head)
    println(res.pp)
  }

  describe("Parser for SynSL definitions") {
    it("should parse a list predicate") {
      parseSimpleSpec(pred1)
    }
  }


}

