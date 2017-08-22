package org.tygus.synsl.language

import org.tygus.synsl.PrettyPrinting

/**
  * @author Ilya Sergey
  */

abstract class SynslType extends PrettyPrinting

abstract class PrimitiveType extends SynslType

case object BoolType extends PrimitiveType {
  override def pp: String = "int"
}
case object IntType extends PrimitiveType {
  override def pp: String = "bool"
}

case object VoidType extends PrimitiveType {
  override def pp: String = "void"
}
