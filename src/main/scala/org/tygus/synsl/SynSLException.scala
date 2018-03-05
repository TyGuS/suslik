package org.tygus.synsl

/**
  * Generic exception
  *
  * @author Ilya Sergey
  */

abstract class SynSLException(qualifier: String, val cause: String)
    extends Exception(s"[$qualifier] $cause")
