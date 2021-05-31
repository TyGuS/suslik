
organization := "org.tygus"

name := "suslik"

version := "0.1.0"

scalaVersion := "2.12.12"

javacOptions ++= Seq("-source", "1.8", "-target", "1.8", "-Xlint")
scalacOptions += "-target:jvm-1.8"

resolvers in ThisBuild ++= Seq(
    Resolver.sonatypeRepo("releases"),
    Resolver.sonatypeRepo("snapshots")
)

resolvers += Resolver.bintrayIvyRepo("com.eed3si9n", "sbt-plugins")

lazy val akkaHttpVersion = "10.2.4"
lazy val akkaVersion    = "2.6.14"

libraryDependencies ++= Seq(
  "org.slf4j" % "slf4j-api" % "1.6.4" withSources(),
  "ch.qos.logback" % "logback-classic" % "1.1.3" % "test",
  "org.scalatest" %% "scalatest" % "3.0.1" % "test",
  "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2" withSources(),
  "org.scalaz" %% "scalaz-core" % "7.2.11",
  "com.github.scopt" %% "scopt" % "3.7.0",
  "com.typesafe.scala-logging" %% "scala-logging" % "3.7.2",
  "com.lihaoyi" %% "upickle" % "1.3.15",
  "org.bitbucket.franck44.scalasmt" %% "scalasmt" % "2.1.1-SNAPSHOT" withSources(),
  // Server stuff
  "com.typesafe.akka" %% "akka-http" % akkaHttpVersion,
  "com.typesafe.akka" %% "akka-stream" % akkaVersion,
  "com.typesafe.akka" %% "akka-actor-typed" % akkaVersion
)

scalacOptions ++= Seq()

logLevel in ThisBuild := Level.Warn

//  creating a logger and setting level to warn/whatever for console
initialCommands in console :=
    """|
       | import ch.qos.logback.classic.Logger
       | import org.slf4j.LoggerFactory
       | val root = LoggerFactory.getLogger("root").asInstanceOf[Logger]
       | import ch.qos.logback.classic.Level
       | root.setLevel(Level.OFF)
       | """.stripMargin

mainClass in assembly := Some("org.tygus.suslik.synthesis.SynthesisRunner")

test in assembly := {}

parallelExecution in Test := false

assemblyJarName in assembly := "suslik.jar"

assemblyMergeStrategy in assembly := {
 case PathList("META-INF", xs @ _*) => MergeStrategy.discard
 case x => MergeStrategy.first
}
