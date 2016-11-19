package soot.heapshape

import scala.collection.{immutable => im}

trait HeapShapeAnalysis {
  def getPredecessors(ref: Reference) : im.Set[Reference]
}
