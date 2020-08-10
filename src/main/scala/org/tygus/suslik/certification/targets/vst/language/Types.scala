package org.tygus.suslik.certification.targets.vst.language

object Types {


  sealed trait AnalysisVSTTypes extends PrettyPrinting {

    /** the Analysis VST type encodes more precise information about pointers
      * than is stored in a VST proof - after the analysis, we can drop this
      * additional information */
    def downcast : VSTType = this match {
      case tType: VSTType => tType
      case _: PtrType => CVoidPtrType
      case pureType: PureType =>pureType.asInstanceOf[VSTType]
    }
  }

  /** types used in a VST program  */
  sealed abstract class VSTType extends PrettyPrinting with AnalysisVSTTypes
  sealed trait PtrType extends AnalysisVSTTypes
  sealed trait PureType extends AnalysisVSTTypes

  case object CBoolType extends VSTType with PureType {
    override def pp: String = "bool"
  }

  case object CIntType extends VSTType with PureType {
    override def pp: String = "int"
  }

  case object CUnitType extends VSTType with PureType {
    override def pp: String = "void"
  }

  /** encoding of void pointer types */
  case object CVoidPtrType extends VSTType with PureType {
    override def pp: String = s"void *"
  }

  // the following types are only used in the program analysis, so don't form part of the
  // VSTType hierarchy, but can be used to track additional information

  /** encoding of void **  pointer types */
  case object CVoidPtrPtrType extends PtrType with PrettyPrinting {
    override def pp: String = s"void **"
  }
  /** encoding of int*  pointer types */
  case object CIntPtrType extends PtrType with PrettyPrinting {
    override def pp: String = s"int *"
  }
  /** encoding of bool*  pointer types */
  case object CBoolPtrType extends PtrType with PrettyPrinting {
    override def pp: String = s"bool *"
  }

  def deref_type(ptrType: PtrType) = ptrType match {
    case CVoidPtrPtrType => CVoidPtrType
    case CIntPtrType => CIntType
    case CBoolPtrType => CBoolType
  }

  def ptr_type(elem_type: PureType) = elem_type match {
    case CBoolType => CBoolPtrType
    case CIntType => CIntPtrType
    case CUnitType => CVoidPtrType
    case CVoidPtrType => CVoidPtrPtrType
  }
}
