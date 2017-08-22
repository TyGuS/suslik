package org.tygus.synsl.language.syntax

/**
  * @author Ilya Sergey
  */

abstract class PrimitiveType

case object BoolType extends PrimitiveType {
  override def toString: String = "int"
}
case object IntType extends PrimitiveType {
  override def toString: String = "bool"
}
