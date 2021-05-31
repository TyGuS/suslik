package org.tygus.suslik.interaction

import akka.actor.typed.ActorSystem
import akka.actor.typed.scaladsl.Behaviors
import akka.http.scaladsl.Http
import akka.http.scaladsl.server.Route
import akka.http.scaladsl.server.Directives._
import org.tygus.suslik.synthesis.{SynConfig, SynthesisRunner}

import scala.util.{Failure, Success}


class SynthesisServer {

  val runner = SynthesisRunner
  val config = SynConfig()

  def start(): Unit = { //
    val root = Behaviors.setup[Nothing] { context =>
      implicit val system: ActorSystem[Nothing] = context.system
      startHttpServer(routes)(context.system)
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

  def routes = {
    pathPrefix("go") {
      pathEnd {
        get {
          complete(go())
        }
      }
    }
  }
}

object SynthesisServer {
  def main(args: Array[String]): Unit = {
    val server = new SynthesisServer
    server.start()
  }
}
