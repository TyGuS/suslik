package org.tygus.suslik.synthesis

import java.io.File

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.certification.targets.vst.VST
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.report.StopWatch.timed

case class CertificationExports(target: CertificationTarget, export_folder: String, common_name: String = "common") extends CertificationBenchmarks {
  override val targets: List[CertificationTarget] = List(target)

  def dump_all_tests(base_dir: String, test_folder: String): Unit = {
    println(s"=========================================\n")
    println(s"  Benchmark Group: $test_folder\n")
    println(s"=========================================\n")
    val path = List(rootDir, base_dir, test_folder).mkString(File.separator)
    val testDir = new File(path)
    val export_path = List(export_folder, test_folder).mkString(File.separator)
    val export_dir = new File(export_path)
    export_dir.mkdirs()

    if (testDir.exists() && testDir.isDirectory) {
      print(s"Retrieving definitions and specs from ${testDir.getName}...")
      val defs = getDefs(testDir.listFiles.filter(f => f.isFile && f.getName.endsWith(s".$defExtension")).toList)
      val tests = testDir.listFiles.filter(f => f.isFile && (f.getName.endsWith(s".$testExtension") || f.getName.endsWith(s".$sketchExtension"))).toList
      println("done!")

      val parser = new SSLParser

      val testCases = for (f <- tests) yield {
        val (testName, desc, in, out, params) = getDescInputOutput(f.getAbsolutePath)
        (testName, in, params)
      }

      println(s"\n****************************************\n")
      println(s"Running benchmarks for certification target: ${target.name}")
      println(s"Initialized output directory: ${export_dir.getCanonicalPath}\n")
      println(s"Synthesizing ${tests.length} test cases...")
      val synResults = for ((testName, in, params) <- testCases) yield {
        println(s"$testName:")
        val fullInput = List(defs, in).mkString("\n")
        print(s"  synthesizing in certification mode...")
        val (res, env, synDuration) = synthesizeOne(fullInput, parser, params.copy(assertSuccess = false))
        print(s"  generating certificate...")
        try {
          val (cert, proofGenDuration) = timed(target.certify(res.head, env))
          println("done!")
          (testName, synDuration, Some(cert, proofGenDuration))
        } catch {
          case e =>
            println(s"- ERR\n   failed to generate certificate for ${testName} (${e.getLocalizedMessage})")
            (testName, synDuration, None)
        }
      }
      println(s"Successfully synthesized ${tests.length} tests.")

      val validCerts = synResults.map(_._3).filter(_.isDefined).map(_.get).map(_._1)
      val predicates = validCerts.flatMap(_.predicates).groupBy(_.name).map(_._2.head).toList
      val defFiles = target.generate_common_definitions_of(defFilename, predicates)
      defFiles.foreach {
        case output =>
          print(s"\nWriting common definitions to file $export_path/${output.filename}...")
          serialize(export_dir, output.filename, output.body)
      }
      println("done!")


      synResults.foreach { case (testName, synDuration, certOpt) => certOpt match {
        case None => ()
        case Some((cert, proofGenDuration)) =>
          val outputs = cert.outputs_with_common_predicates(defFilename, predicates)
          for (o <- outputs) yield {
            print(s"  Writing certificate output to file ${o.filename}...")
            serialize(export_dir, o.filename, o.body)
          }
      }
      }
    }
  }
}
object VSTCertificationExports {
  def main(args: Array[String]): Unit = {
    val benchmarks = CertificationExports(VST(), "/tmp/benchmarks")
    benchmarks.initLog()
    benchmarks.dump_all_tests("certification-benchmarks", "ints")
    benchmarks.dump_all_tests("certification-benchmarks", "sll-bounds")
    benchmarks.dump_all_tests("certification-benchmarks", "sll")
    benchmarks.dump_all_tests("certification-benchmarks", "dll")
    benchmarks.dump_all_tests("certification-benchmarks", "tree")
  }
}