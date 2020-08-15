package org.tygus.suslik.certification.targets.vst.language

object CTypes {


  sealed trait AnalysisVSTTypes extends PrettyPrinting {

    /** the Analysis VST type encodes more precise information about pointers
      * than is stored in a VST proof - after the analysis, we can drop this
      * additional information */
    def downcast : VSTCType = this match {
      case tType: VSTCType => tType
      case _: PtrType => CVoidPtrType
      case pureType: PureType =>pureType.asInstanceOf[VSTCType]
    }
  }

  /** types used in a C program  */
  sealed abstract class VSTCType extends PrettyPrinting with AnalysisVSTTypes
  sealed trait PtrType extends AnalysisVSTTypes
  sealed trait PureType extends AnalysisVSTTypes

  case object CIntType extends VSTCType with PureType {
    override def pp: String = "int"
  }

  case object CUnitType extends VSTCType with PureType {
    override def pp: String = "void"
  }

  /** encoding of void pointer types */
  case object CVoidPtrType extends VSTCType with PureType {
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

  def deref_type(ptrType: PtrType) = ptrType match {
    case CVoidPtrPtrType => CVoidPtrType
    case CIntPtrType => CIntType
  }

  def ptr_type(elem_type: PureType) = elem_type match {
    case CIntType => CIntPtrType
    case CUnitType => CVoidPtrType
    case CVoidPtrType => CVoidPtrPtrType
  }
}
