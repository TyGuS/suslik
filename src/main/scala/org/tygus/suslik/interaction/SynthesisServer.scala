package org.tygus.suslik.interaction

import akka.NotUsed

import java.util.concurrent.ArrayBlockingQueue
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}
import akka.actor.typed.ActorSystem
import akka.actor.typed.scaladsl.Behaviors
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.ws.{BinaryMessage, Message, TextMessage}
import akka.http.scaladsl.server.Route
import akka.http.scaladsl.server.Directives._
import akka.stream.scaladsl.{Flow, Sink, Source}
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

  def go(session: SynthesisRunnerUtil = runner): String = {
    val dir = "./src/test/resources/synthesis/all-benchmarks/sll" /** @todo */
    val fn = "free.syn"
    session.synthesizeFromFile(dir, fn, config).toString()
  }

  private def routes(implicit system: ActorSystem[_]) = {
    import system.executionContext
    concat(
      pathSingleSlash {
        concat(
          handleWebSocketMessages({
            val session = new ClientSessionSynthesis()
            new Thread(() => go(session)).start()
            session.wsFlow
          }),
          get {
            new Thread(() => go()).start(); complete(".")
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

/**
  * A synthesizer that sends and receives choices via async queues.
  * Data is serialized in and out using a JSON format.
  */
class AsyncSynthesisRunner extends SynthesisRunnerUtil {
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
          allExpansions.find(_.subgoals.isEmpty) match {
            case Some(fin) => Seq(fin)
            case _ =>
              outbound.put(write(allExpansions.map(_.subgoals.map(GoalEntry(_)))))
              val choice = inbound.take()
              allExpansions.filter(_.subgoals.exists(goal => goal.label.pp.contains(choice)))
          }
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

/**
  * Connects `AsyncSynthesisRunner` to an HTTP client.
  */
class ClientSessionSynthesis extends AsyncSynthesisRunner {

  def subscribe(implicit ec: ExecutionContext): Source[String, _] =
    Source.unfoldAsync(())(_ => Future {
      try Some((), outbound.take())
      catch { case _: InterruptedException => None }
    })

  def offer(implicit ec: ExecutionContext): Sink[String, _] =
    Sink.foreachAsync[String](1)(s => Future { inbound.put(s) })

  def wsFlow(implicit ec: ExecutionContext): Flow[Message, Message, NotUsed] =
    Flow.fromSinkAndSource(Flow[Message].mapConcat {
        case m: TextMessage.Strict => println(m.text); List(m.text)
        case _ => println("some other message"); Nil
      }.to(offer),
      subscribe.map(TextMessage(_)))
}