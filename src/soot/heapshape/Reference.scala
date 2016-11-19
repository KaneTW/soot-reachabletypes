package soot.heapshape

import soot.jimple

trait Reference extends Any

case class Local(v: soot.Local) extends AnyVal with Reference
case class ArrayRef(v: jimple.ArrayRef) extends AnyVal with Reference
case class InstanceFieldRef(v: jimple.InstanceFieldRef) extends AnyVal with Reference
case class StaticFieldRef(v: jimple.StaticFieldRef) extends AnyVal with Reference

