package org.tygus.suslik.report

import scala.concurrent.duration.Duration


/**
  * Formatting of tabular data for textual output
  *
  * @param data list of row data
  * @tparam T cell data type
  */
class Table[T](val data: List[List[Option[T]]]) {
  def this(data: List[List[T]])(implicit dummy: DummyImplicit) = this(data.map(_.map(Some(_))))

  override def toString = if (data.isEmpty) "" else {
    val ncols = data.map(_.length).max
    val str = data.map(_.map(formatCell).padTo(ncols, ""))
    val colWidths = (0 until ncols).map(i => str.map(_(i).length).max)
    str.map(_.zip(colWidths)
      .map { case (text, width) => text.padTo(width, ' ') } .mkString("  ")
    ).mkString("\n")
  }
  private def formatCell(v: Option[T]) = v.map(toStringSafe).getOrElse("")
  private def toStringSafe(o: Any) = if (o == null) "(null)" else o.toString

  def withTotals(cols: Seq[Int], aggregate: Seq[T] => T): Table[T] = if (cols.isEmpty) this else {
    val sums = cols.map(i => i -> aggregate(data.map(_(i)).collect { case Some(v) => v })).toMap
    val row = (0 to cols.max).map(sums.get).toList
    new Table[T](data :+ row)
  }
}

object Table {
  trait Summable[T] { val zero: T; def plus(x: T, y: T): T }

  def sumNum[T](d: Seq[Any])(implicit num: Numeric[T]): T = d.map(_.asInstanceOf[T]).sum
  def sum[T](d: Seq[Any])(implicit s: Summable[T]): T = d.map(_.asInstanceOf[T]).foldLeft(s.zero)(s.plus)
}