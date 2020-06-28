package org.tygus.suslik.report

import java.util.Date
import scala.collection.mutable

import org.tygus.suslik.report.Table.Summable


/**
  * An auxiliary class for measuring how long operations take to complete.
  */
class StopWatch {
  var init: Long = 0
  var from: Long = 0
  var elapsed: Long = 0

  private var running: Int = 0

  import StopWatch._

  def reset(): Unit = {
    init = 0
    from = 0
    elapsed = 0
  }

  def nowMs: Long = {
    val ctm = System.currentTimeMillis()
    if (init == 0) init = ctm
    ctm
  }

  def now: Instant = {
    val ctm = nowMs
    Instant(ctm - init, new Date(ctm))
  }

  def start() {
    if (running == 0) from = nowMs; running += 1
  }

  def stop() {
    running -= 1; if (running == 0) elapsed += (nowMs - from)
  }

  def timed[T](op: => T): T =
    try {
      start(); op
    } finally {
      stop()
    }
}


object StopWatch {

  lazy val instance = new StopWatch

  case class Instant(offset: Long, time: Date) {
    override def toString: String = s"${time} [+${offset}]"
  }

  case class DurationMs(ms: Long) {
    override def toString: String = s"${ms}ms"
    def +(other: DurationMs): DurationMs = DurationMs(ms + other.ms)
  }

  implicit object DurationMsIsSummable extends Summable[DurationMs] {
    override val zero: DurationMs = DurationMs(0)
    override def plus(x: DurationMs, y: DurationMs): DurationMs = x + y
  }

  class FactoryMap[K, V] extends mutable.HashMap[K, V] {
    override def apply(key: K): V = {
      val result = findEntry(key)
      if (result eq null) {
        val v = default(key); put(key, v); v
      }
      else result.value
    }
  }

  object factory extends FactoryMap[String, StopWatch] {
    override def default(key: String) = new StopWatch
  }

  def summary: Table[_] =
    new Table((for ((k, v) <- factory) yield List(k, DurationMs(v.elapsed))).toList)
      .withTotals(Seq(1), Table.sum[DurationMs])

  def timed[T](op: => T): (T, Long) = {
    val t1 = System.currentTimeMillis()
    val res = op
    val t2 = System.currentTimeMillis()
    (res, t2 - t1)
  }

}


trait LazyTiming {
  protected def watchName: String = getClass.getSimpleName

  @transient
  protected lazy val watch: StopWatch = StopWatch.factory(watchName)

  def timed[T](op: => T): T = watch.timed(op)

  def elapsed: Long = watch.elapsed

  def reset() = watch.from
}