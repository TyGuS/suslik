
organization := "org.tygus"

name := "synsl"

version := "0.5.0"

scalaVersion := "2.12.5"

val akkaVersion = "2.5.3"

resolvers in ThisBuild ++= Seq(
    Resolver.sonatypeRepo("releases"),
    Resolver.sonatypeRepo("snapshots")
)

libraryDependencies ++= Seq(
  // "com.typesafe.akka" %% "akka-actor" % akkaVersion,
  // "com.typesafe.akka" %% "akka-slf4j" % akkaVersion % "test",
  // "com.typesafe.akka" %% "akka-testkit" % akkaVersion % "test",
  // "com.regblanc" %% "scala-smtlib" % "0.2.2",
  "org.slf4j" % "slf4j-api" % "1.6.4" withSources(),
  "ch.qos.logback" % "logback-classic" % "1.1.3" % "test",
  "org.scalatest" %% "scalatest" % "3.0.1" % "test",
  "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.6" withSources(),
  "org.scalaz" %% "scalaz-core" % "7.2.11",
  "com.typesafe.scala-logging" %% "scala-logging" % "3.7.2",
  "org.bitbucket.franck44.scalasmt" %% "scalasmt" % "2.1.0" withSources()
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

