package org.tygus.suslik.language

/**
  * @author Ilya Sergey
  */

abstract class SynslType extends PrettyPrinting {
  def supertype(target: Option[SynslType]): Option[SynslType] = target match {
    case None => Some(this)
    case Some(t1) if this == t1 => Some(this)
    case Some(IntType) if this == LocType => Some(this)
    case Some(LocType) if this == IntType => Some(LocType)
    case _ => None
  }

  def conformsTo(target: Option[SynslType]): Boolean = supertype(target).isDefined

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