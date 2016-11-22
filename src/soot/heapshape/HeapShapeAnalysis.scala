package soot.heapshape

import soot.Value

// Value should be replaced with a stronger refined type
trait HeapShapeAnalysis {
  def getPredecessors(ref: Value) : collection.Set[Value]
}
