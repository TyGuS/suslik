package org.tygus.suslik.certification.traversal

import org.tygus.suslik.certification.traversal.Context._
import org.tygus.suslik.certification.traversal.Step.DestStep

import scala.collection.immutable.Queue

/**
  * Composable and stackable evaluation context
  *
  */
case class Context[S <: DestStep[S]](deferreds: Queue[AbstractDeferred[S]], tricks: List[AbstractTrick[S]]) {
  def +(that: Context[S]): Context[S] = Context(deferreds ++ that.deferreds, tricks ++ that.tricks)
}

object Context {
  type AbstractTrick[S <: DestStep[S]]
  type AbstractDeferred[S <: DestStep[S]] = List[AbstractTrick[S]] => S

  abstract class Action
  case object Push extends Action
  case object Pop extends Action
  case object Replace extends Action
}
