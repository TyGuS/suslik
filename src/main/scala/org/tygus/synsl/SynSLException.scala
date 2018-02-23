package org.tygus.synsl

/**
  * Generic exception
  *
  * @author Ilya Sergey
  */

abstract class SynSLException(qualifier: String, private val msg: String)
    extends Exception(s"[$qualifier] $msg")
