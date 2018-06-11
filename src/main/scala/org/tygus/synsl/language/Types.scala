package org.tygus.synsl.language

/**
  * @author Ilya Sergey
  */

abstract class SynslType extends PrettyPrinting

case object BoolType extends SynslType {
  override def pp: String = "bool"
}

case object IntType extends SynslType {
  override def pp: String = "int"
}

case object LocType extends SynslType {
  override def pp: String = "loc"
}

case object IntSetType extends SynslType {
  override def pp: String = "set"
}

case object VoidType extends SynslType {
  override def pp: String = "void"
}