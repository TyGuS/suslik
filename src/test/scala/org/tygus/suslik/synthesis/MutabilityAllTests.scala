package org.tygus.suslik.synthesis

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis

class MutabilityAllTests extends FunSpec with Matchers with SynthesisRunnerUtil {

    val synthesis: Synthesis = new PhasedSynthesis

    def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(desc) {
        synthesizeFromSpec(testName, in, out, params)
    }

    describe("") {
        runAllTestsFromDir("../immutable-synthesis")
    }

    describe("abduct") {
        runAllTestsFromDir("../immutable-synthesis/abduct")
    }

    describe("beyond") {
        runAllTestsFromDir("../immutable-synthesis/beyond")
    }

    describe("copy") {
        runAllTestsFromDir("../immutable-synthesis/copy")
    }

    describe("copy-len") {
        runAllTestsFromDir("../immutable-synthesis/copy-len")
    }

    describe("dllist") {
        runAllTestsFromDir("../immutable-synthesis/dllist")
    }

    describe("entail") {
        runAllTestsFromDir("../immutable-synthesis/entail")
    }

    describe("failing-examples") {
        runAllTestsFromDir("../immutable-synthesis/failing-examples")
    }

    describe("flatten") {
        runAllTestsFromDir("../immutable-synthesis/flatten")
    }

    describe("llist") {
        runAllTestsFromDir("../immutable-synthesis/llist")
    }

    describe("paper-benchmarks") {
        runAllTestsFromDir("../immutable-synthesis/paper-benchmarks")
    }

    describe("paper-examples") {
        runAllTestsFromDir("../immutable-synthesis/paper-examples")
    }

    describe("sets") {
        runAllTestsFromDir("../immutable-synthesis/sets")
    }

    describe("simple") {
        runAllTestsFromDir("../immutable-synthesis/simple")
    }

    describe("tree") {
        runAllTestsFromDir("../immutable-synthesis/tree")
    }

}
