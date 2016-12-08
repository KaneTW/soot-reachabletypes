package soot.cg.utils

import soot.{MethodOrMethodContext, SootMethod}
import soot.jimple.toolkits.callgraph.CallGraph
import soot.toolkits.graph.{DirectedGraph, HashMutableDirectedGraph, MutableDirectedGraph, StronglyConnectedComponentsFast}

import scala.collection.JavaConverters._
import scala.collection.{immutable, mutable}

object CallGraphUtils {

  type DirectedCallGraph = MutableDirectedGraph[SootMethod]

  implicit class AsDirectedGraph(val cg: CallGraph) extends AnyVal {
    def asDirectedGraph : DirectedCallGraph = {
      val graph = new HashMutableDirectedGraph[SootMethod]()
      for (elem <- cg.iterator().asScala) {
        // scala ambiguous reference
        if (!graph.containsNode(elem.src().asInstanceOf[Any])) {
          graph.addNode(elem.src())
        }

        if (!graph.containsNode(elem.tgt().asInstanceOf[Any])) {
          graph.addNode(elem.tgt())
        }

        if (!graph.containsEdge(elem.src(), elem.tgt())) {
          graph.addEdge(elem.src(), elem.tgt())
        }
      }

      graph
    }
  }

  def removeCycles(cg: DirectedCallGraph): Unit = {

    val sccs = new StronglyConnectedComponentsFast(cg).getTrueComponents.asScala.flatMap(_.asScala)

    for (elem <- sccs) {
      cg.removeNode(elem)
    }
  }

}