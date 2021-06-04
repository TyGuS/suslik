package org.tygus.suslik.interaction

import java.util.concurrent.ArrayBlockingQueue
import scala.concurrent.ExecutionContext
import scala.util.{Failure, Success}
import akka.actor.typed.ActorSystem
import akka.actor.typed.scaladsl.Behaviors
import akka.http.scaladsl.Http
import akka.http.scaladsl.server.Route
import akka.http.scaladsl.server.Directives._

import org.tygus.suslik.language.Statements
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.report.ProofTraceJson
import org.tygus.suslik.synthesis.rules.Rules
import org.tygus.suslik.synthesis.tactics.PhasedSynthesis
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisRunnerUtil}



class SynthesisServer {

  val runner = new ClientSessionSynthesis
  val config: SynConfig = SynConfig()

  def start(): Unit = { //
    val root = Behaviors.setup[Nothing] { context =>
      implicit val system: ActorSystem[Nothing] = context.system
      import system.executionContext
      //ClientSessionSynthesis.initQueue
      startHttpServer(routes)
      Behaviors.empty
    }
    ActorSystem[Nothing](root, "SynthesisServer")
  }

  private def startHttpServer(routes: Route)(implicit system: ActorSystem[_]): Unit = {
    import system.executionContext
    Http().newServerAt("localhost", 8080).bind(routes)
      .onComplete {
        case Success(binding) =>
          val address = binding.localAddress
          system.log.info("Server online at http://{}:{}/", address.getHostString, address.getPort)
        case Failure(ex) =>
          system.log.error("Failed to bind HTTP endpoint, terminating system", ex)
          system.terminate()
      }
  }

  def go(): String = {
    val fn = "./src/test/resources/synthesis/simple/free.syn" /** @todo */
    runner.synthesizeFromFile("" /* ignored :( */, fn, config).toString()
  }

  private def routes(implicit ctx: ExecutionContext) = {
    concat(
      pathSingleSlash {
        new Thread(() => { go() }).start(); complete(".")
      },
      pathPrefix("next") {
        concat(
          get {
            complete(runner.outbound.take())
          },
          post {
            entity(as[String]) { choice =>
              runner.inbound.put(choice)
              complete(".")
            }
          }
        )
      }
    )
  }
}

object SynthesisServer {
  def main(args: Array[String]): Unit = {
    val server = new SynthesisServer
    server.start()
  }
}

class ClientSessionSynthesis extends SynthesisRunnerUtil {
  import org.tygus.suslik.report.ProofTraceJson._
  import upickle.default.{Writer, write}

  val inbound = new ArrayBlockingQueue[String](1)
  val outbound = new ArrayBlockingQueue[String](1)

  /**
    * Creates a `PhasedSynthesizer` that expands goals based on input sent
    * from the client (through `inbound`) and reports everything back to the
    * client in JSON format (through `outbound`).
    * @param env synthesis environment
    * @return a configured `Synthesis` instance
    */
  override def createSynthesizer(env: Environment): Synthesis = {
    val tactic =
      new PhasedSynthesis(env.config) {
        override def filterExpansions(allExpansions: Seq[Rules.RuleResult]): Seq[Rules.RuleResult] = {
          outbound.put(write(allExpansions.map(_.subgoals.map(GoalEntry(_)))))
          val choice = inbound.take()
          allExpansions.filter(_.subgoals.exists(goal => goal.label.pp.contains(choice)))
        }
      }
    val trace = new ProofTraceJson {
      override protected def writeObject[T](t: T)(implicit w: Writer[T]): Unit =
        outbound.put(write(t))
    }
    new Synthesis(tactic, log, trace)
  }

  /**
    * Wraps parent implementation, reporting success or failure to the client.
    * @todo make results be JSON
    */
  override def synthesizeFromSpec(testName: String, text: String, out: String,
                                  params: SynConfig): List[Statements.Procedure] = {
    try {
      val ret = super.synthesizeFromSpec(testName, text, out, params)
      outbound.put(ret.toString)
      ret
    }
    catch { case e: Throwable => outbound.put(e.toString); throw e }
  }
}