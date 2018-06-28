package org.tygus.synsl.language

/**
  * @author Ilya Sergey
  */

abstract class SynslType extends PrettyPrinting {
  def conformsTo(target: Option[SynslType]): Boolean = target match {
    case None => true
    case Some(t1) if this == t1 => true
    case Some(IntType) => this == LocType
    case Some(LocType) => this == IntType
    case _ => false
  }
}

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
  override def pp: String = "intset"
}

case object VoidType extends SynslType {
  override def pp: String = "void"
}