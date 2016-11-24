package soot.heapshape

import soot.{SootMethod, Value, Unit => SUnit}


// Value should be replaced with a stronger refined type
trait HeapShapeAnalysis {
  def getPredecessors(method: SootMethod, unit: SUnit, ref: Value) : collection.Set[Value]
}
