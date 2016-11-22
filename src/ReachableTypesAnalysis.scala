
import java.util

import soot.heapshape.HeapShapeAnalysis
import soot.jimple._
import soot.options.Options
import soot.toolkits.graph.{DirectedGraph, ExceptionalUnitGraph}
import soot.toolkits.scalar.ForwardFlowAnalysis
import soot.{Body, BodyTransformer, Local, PackManager, Scene, Transform, Value, Type => SType, Unit => SUnit}

import scala.collection.JavaConverters._
import scala.collection.{mutable => m}




// refactor into trait later
class ReachableTypesAnalysis(heapShapeAnalysis: HeapShapeAnalysis, g: DirectedGraph[SUnit]) extends ForwardFlowAnalysis[SUnit, m.Map[Value, m.Set[SType]]](g) {
  doAnalysis()

  override def flowThrough(before: m.Map[Value, m.Set[SType]], n: SUnit, after: m.Map[Value, m.Set[SType]]): Unit = {
    val pta = Scene.v().getPointsToAnalysis
    copy(before, after)


    def possibleTypesOf(v: Value): m.Set[SType] = v match {
      case v: Local =>
        before.getOrElse(v, pta.reachingObjects(v).possibleTypes().asScala)
      case v: StaticFieldRef =>
        before.getOrElse(v, pta.reachingObjects(v.getField).possibleTypes().asScala)
      case v: InstanceFieldRef =>
        v.getBase match {
          case base: Local =>
            before.getOrElse(v, pta.reachingObjects(base, v.getField).possibleTypes().asScala)
          case _ => throw new RuntimeException("Expected Local base for InstanceFieldRef")
        }
      case v: ArrayRef =>
        possibleTypesOf(v.getBase)

      case _ => m.HashSet(v.getType)
    }

    def updateAfter(newSet: m.Set[SType])(left: Value) : Unit = {
      val old = after.getOrElse(left, m.Set())
      after.put(left, old ++ newSet)
    }

    n match {
      case n: DefinitionStmt =>
        val left = n.getLeftOp
        val rightTypes = possibleTypesOf(n.getRightOp)
        val updateFunc = updateAfter(rightTypes)
        updateFunc(left)
        heapShapeAnalysis.getPredecessors(left).foreach(updateFunc)

      case _ =>
    }
  }

  override def merge(in1: m.Map[Value, m.Set[SType]], in2: m.Map[Value, m.Set[SType]], out: m.Map[Value, m.Set[SType]]): Unit = {
    out ++= in1
    in2.foreach { case (k, v) =>
      val old = out.getOrElse(k, m.Set())
      out(k) = v ++ old
    }
  }

  override def newInitialFlow(): m.Map[Value, m.Set[SType]] = m.Map()

  override def copy(in: m.Map[Value, m.Set[SType]], out: m.Map[Value, m.Set[SType]]): Unit = {
    out ++= in
  }

}

object ReachableTypesExtension {
  def main(args: Array[String]): Unit = {
    Options.v().set_whole_program(true)
    Options.v().setPhaseOption("cg.spark", "on")

    val jtpPack = PackManager.v().getPack("jtp")
    jtpPack.add(
      new Transform("jtp.reachableTypesTransform", new BodyTransformer() {
        def internalTransform(body: Body, phase: String, options: util.Map[String, String]): Unit = {
          val ana = new ReachableTypesAnalysis(null, new ExceptionalUnitGraph(body))
          System.out.println(body)
          System.out.println(ana.getFlowAfter(body.getUnits.getLast))
        }
      }))

    soot.Main.main(args)
  }
}
