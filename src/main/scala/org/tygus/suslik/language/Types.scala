package org.tygus.suslik.language

/**
  * @author Ilya Sergey
  */

abstract class SSLType extends PrettyPrinting {
  def supertype(target: Option[SSLType]): Option[SSLType] = target match {
    case None => Some(this)
    case Some(t1) if this == t1 => Some(this)
    case _ => None
  }

  def subtype(target: Option[SSLType]): Option[SSLType] = supertype(target)

  def conformsTo(target: Option[SSLType]): Boolean = supertype(target).isDefined

  def isSubtypeOf(other: SSLType): Boolean = supertype(Some(other)).contains(other)
}

case object BoolType extends SSLType {
  override def pp: String = "bool"

}

case object IntType extends SSLType {
  override def pp: String = "int"

  override def supertype(target: Option[SSLType]): Option[SSLType] = target match {
    case None => Some(this)
    case Some(LocType) => Some(LocType)
    case Some(IntType) => Some(this)
    case Some(CardType) => Some(this)
    case _ => None
  }

  override def subtype(target: Option[SSLType]): Option[SSLType] = target match {
    case None => Some(this)
    case Some(LocType) => Some(this)
    case Some(IntType) => Some(this)
    case Some(CardType) => Some(CardType)
    case _ => None
  }

}

case object LocType extends SSLType {
  override def pp: String = "loc"

  override def supertype(target: Option[SSLType]): Option[SSLType] = target match {
    case None => Some(this)
    case Some(LocType) => Some(this)
    case Some(IntType) => Some(this)
    case Some(CardType) => Some(this)
    case _ => None
  }

  override def subtype(target: Option[SSLType]): Option[SSLType] = target match {
    case None => Some(this)
    case Some(LocType) => Some(this)
    case Some(IntType) => Some(IntType)
    case Some(CardType) => Some(CardType)
    case _ => None
  }
}

case object IntSetType extends SSLType {
  override def pp: String = "intset"
}

case object IntervalType extends SSLType {
  override def pp: String = "interval"
}

case object VoidType extends SSLType {
  override def pp: String = "void"
}

case object CardType extends SSLType {
  override def pp: String = "card"

  override def supertype(target: Option[SSLType]): Option[SSLType] = target match {
    case None => Some(this)
    case Some(LocType) => Some(LocType)
    case Some(IntType) => Some(IntType)
    case Some(CardType) => Some(this)
    case _ => None
  }

  override def subtype(target: Option[SSLType]): Option[SSLType] = target match {
    case None => Some(this)
    case Some(LocType) => Some(this)
    case Some(IntType) => Some(this)
    case Some(CardType) => Some(this)
    case _ => None
  }
}

case object IntSequenceType extends SSLType {
  override def pp: String = "intseq"
}
