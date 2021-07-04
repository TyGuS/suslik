package org.tygus.suslik.interaction

import java.util.concurrent.ArrayBlockingQueue
import scala.concurrent.{ExecutionContext, Future}
import scala.util.{Failure, Success}
import org.slf4j.Logger
import upickle.default.{macroRW, ReadWriter => RW}
import akka.{Done, NotUsed}
import akka.actor.typed.ActorSystem
import akka.actor.typed.scaladsl.Behaviors
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.ws.{Message, TextMessage}
import akka.http.scaladsl.server.Route
import akka.http.scaladsl.server.Directives._
import akka.stream.scaladsl.{Flow, Keep, Sink, Source}
import org.tygus.suslik.interaction.AsyncSynthesisRunner.ChooseMessage
import org.tygus.suslik.language.Statements
import org.tygus.suslik.logic.{Environment, FunSpec, Specifications}
import org.tygus.suslik.report.{Log, ProofTrace, ProofTraceJson}
import org.tygus.suslik.report.ProofTraceJson.GoalEntry
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId, OrNode}
import org.tygus.suslik.synthesis.Termination.isTerminatingExpansion
import org.tygus.suslik.synthesis.rules.Rules
import org.tygus.suslik.synthesis.tactics._
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisRunner, SynthesisRunnerUtil}
import org.tygus.suslik.util.SynStats


class SynthesisServer {

  val config: SynConfig = SynConfig()

  /* Server configuration */
  protected def port(implicit system: ActorSystem[_]): Int = {
    val envPort = System.getenv("PORT")
    if (envPort != null) Integer.parseInt(envPort)
    else system.settings.config.getInt("suslik.server.port")
  }

  def start(): Unit = {
    val root = Behaviors.setup[Nothing] { context =>
      implicit val system: ActorSystem[_] = context.system
      startHttpServer(routes, port)
      Behaviors.empty
    }
    ActorSystem[Nothing](root, "SynthesisServer")
  }

  /**
    * Server startup boilerplate.
    */
  private def startHttpServer(routes: Route, port: Int)(implicit system: ActorSystem[_]): Unit = {
    import system.executionContext
    Http().newServerAt("0.0.0.0", port).bind(routes)
      .onComplete {
        case Success(binding) =>
          val address = binding.localAddress
          system.log.info("Server online at http://{}:{}/", address.getHostString, address.getPort)
        case Failure(ex) =>
          system.log.error("Failed to bind HTTP endpoint, terminating system", ex)
          system.terminate()
      }
  }

  def go(session: SynthesisRunnerUtil): String = {
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
            session.wsFlow
          }),
          get {
            getFromFile("./dist/index.html")
          }
        )
      },
      getFromDirectory("./dist")
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
  import upickle.default.{Writer, write}
  import AsyncSynthesisRunner._

  val inbound = new ArrayBlockingQueueWithCancel[String](1)
  val outbound = new ArrayBlockingQueueWithCancel[String](1)

  val cached = new collection.mutable.HashMap[NodeId, OrNode]()
  val logger: Logger = org.slf4j.LoggerFactory.getLogger(getClass)

  val config: SynConfig = SynConfig()
  protected var isynth: IterativeUnorderedSynthesis = null

  protected val trace: ProofTraceJson = new ProofTraceJson {
    override def add(node: OrNode): Unit =
    { cached.put(node.id, node); super.add(node) }
    override protected def writeObject[T](t: T)(implicit w: Writer[T]): Unit =
      outbound.put(write(t))
  }

  def goAutomatic(spec: SpecMessage): Unit = {
    new Thread(() => synthesizeFromSpec(spec)).start()
  }

  def goInteractive(spec: SpecMessage): Unit = {
    val specConfig = configFromSpec(spec)
    val (funSpec, env, sketch) = prepareSynthesisTask(textFromSpec(spec), specConfig)
    createSynthesizer(env)  // just to initialize isynth :/

    val initialGoal = Specifications.topLevelGoal(funSpec, env, sketch)
    trace.add(OrNode(Vector(), initialGoal, None))
  }

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
              outbound.put(serializeChoices(allExpansions))
              val choice = inbound.take()
              allExpansions.filter(_.subgoals.exists(goal => goal.label.pp.contains(choice)))
          }
        }
      }

    val stats = new SynStats(2500)
    val config = SynConfig()
    isynth = new IterativeUnorderedSynthesis(new AutomaticSimple(env.config), log, trace)(stats, config)
    new Synthesis(new AutomaticSimple(env.config), log, trace)
    //isynth
  }

  /**
    * Wraps parent implementation, reporting success or failure to the client.
    */
  override def synthesizeFromSpec(testName: String, text: String, out: String,
                                  params: SynConfig): List[Statements.Procedure] =
    wrapError {
      try {
        val ret = super.synthesizeFromSpec(testName, text, out, params)
        outbound.put(write(SynthesisResultEntry(ret.map(_.toString))))
        ret
      }
      catch {
        case _: InterruptedException => List() /* can happen if `inbound` is cancelled */
      }
    }

  def synthesizeFromSpec(spec: SpecMessage): List[Statements.Procedure] =
    synthesizeFromSpec(spec.name, textFromSpec(spec),
                       noOutputCheck, configFromSpec(spec))

  def textFromSpec(spec: SpecMessage): String = (spec.defs :+ spec.in).mkString("\n")

  def configFromSpec(spec: SpecMessage): SynConfig =
    SynthesisRunner.parseParams("." +: spec.params.toArray, config)

  def grow(id: NodeId): Unit =
    cached.get(id).foreach(isynth.grow)

  protected def wrapError[T](op: => T): T = {
    try op catch {
      case e: Throwable =>
        logger.error("Error", e)
        outbound.put(write(SynthesisErrorEntry(e.toString))); throw e
    }
  }

  protected def serializeChoices(allExpansions: Seq[Rules.RuleResult]): String =
    write(allExpansions.map(ExpansionChoiceEntry.from))
}

object AsyncSynthesisRunner {

  class ArrayBlockingQueueWithCancel[E](capacity: Int)
      extends ArrayBlockingQueue[E](capacity) {
    private var waiting: Option[Thread] = None
    override def take(): E = {
      assert(waiting.isEmpty)  /* allow at most one consumer thread */
      waiting = Some(Thread.currentThread())
      try super.take() finally { waiting = None }
    }
    def cancel() { waiting foreach (_.interrupt()) }
  }

  /**
    * Provides a Synthesis object that can be asked to expand nodes on-demand.
    * All expansions are immediately sent to the trace (no nodes are suspended).
    */
  class IterativeUnorderedSynthesis(tactic: Tactic, log: Log, trace: ProofTrace)
                                   (implicit stats: SynStats, config: SynConfig)
      extends Synthesis(tactic, log, trace) {

    def grow(node: OrNode): Unit = {
      val goal = node.goal
      implicit val log: Log = this.log
      implicit val ctx: Log.Context = Log.Context(goal)

      for {
        (e, i) <- expansionsForNode(node).zipWithIndex
        andNode = AndNode(i +: node.id, node, e)
        if isTerminatingExpansion(andNode) // termination check
      } {
        trace.add(andNode, andNode.nChildren)
        for (_ <- 1 to andNode.nChildren) trace.add(andNode.nextChild)
      }
    }

    protected def submitNodes(nodes: Seq[OrNode]): Unit = {
      for (node <- nodes) trace.add(node)
    }
  }

  type GoalLabel = String

  case class ExpansionChoiceEntry(from: Set[GoalLabel],
                                  rule: String,
                                  subgoals: Seq[GoalEntry])

  object ExpansionChoiceEntry {
    def from(rr: Rules.RuleResult): ExpansionChoiceEntry =
      ExpansionChoiceEntry(rr.subgoals.flatMap(_.parent).map(_.label.pp).toSet,
        rr.rule.toString,
        rr.subgoals.map(GoalEntry(_)))

    implicit val rw: RW[ExpansionChoiceEntry] = macroRW
  }

  case class SynthesisResultEntry(procs: Seq[String])
  object SynthesisResultEntry {
    implicit val rw: RW[SynthesisResultEntry] = macroRW
  }

  case class SynthesisErrorEntry(error: String)
  object SynthesisErrorEntry {
    implicit val rw: RW[SynthesisErrorEntry] = macroRW
  }

  /* Messages sent from the client */

  sealed abstract class ClientMessage(val tag: String)
  object ClientMessage { implicit val rw: RW[ClientMessage] = macroRW }

  case class SpecMessage(mode: String = "automatic",
                         name: String, defs: Seq[String], in: String,
                         params: Seq[String] = Seq()) extends ClientMessage("Spec")
  object SpecMessage {
    implicit val rw: RW[SpecMessage] = macroRW
  }

  case class ExpandRequestMessage(id: NodeId) extends ClientMessage("ExpandRequest")
  object ExpandRequestMessage {
    implicit val rw: RW[ExpandRequestMessage] = macroRW
  }

  case class ChooseMessage(choice: String) extends ClientMessage("Choose")
  object ChooseMessage {
    implicit val rw: RW[ChooseMessage] = macroRW
  }
}

/**
  * Connects `AsyncSynthesisRunner` to an HTTP client.
  */
class ClientSessionSynthesis(implicit ec: ExecutionContext) extends AsyncSynthesisRunner {
  import upickle.default.read
  import AsyncSynthesisRunner._

  {
    logger.info("client session started")
  }

  def subscribe: Source[String, _] =
    Source.unfoldAsync(())(_ => Future {
      try Some((), outbound.take())
      catch { case _: InterruptedException => None }
    })

  def offer: Sink[String, Future[Done]] =
    Sink.foreachAsync[String](1) { s => Future { wrapError {
      read[ClientMessage](s) match {
        case sp@SpecMessage(mode, _, _, _, _) => mode match {
          case "automatic" => goAutomatic(sp)
          case "interactive" => goInteractive(sp)
        }
        case ChooseMessage(choice) => inbound.put(choice)
        case ExpandRequestMessage(id) => grow(id)
      }
    }}}

  def done(d: Done): Unit = {
    outbound.cancel(); inbound.cancel()
    logger.info(s"client session ended; $d")
  }

  def wsFlow: Flow[Message, Message, NotUsed] =
    Flow.fromSinkAndSource(Flow[Message].mapConcat {
        case m: TextMessage.Strict => List(m.text)
        case _ => logger.warn("received a non-text message"); Nil
      }.to(offer.mapMaterializedValue(m => m.foreach(done))),
      subscribe.map(TextMessage(_)))
}