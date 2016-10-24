import java.util._

import soot.jimple._
import soot.options.Options
import soot.{Body, BodyTransformer, Local, PackManager, PointsToSet, Scene, Transform, Value, Type => SType, Unit => SUnit}
import soot.toolkits.graph.{DirectedGraph, ExceptionalUnitGraph}
import soot.toolkits.scalar.ForwardFlowAnalysis

/**
  * Created by kane on 10/21/16.
  */

// refactor into trait later
class ReachableTypesAnalysis(g: DirectedGraph[SUnit]) extends ForwardFlowAnalysis[SUnit, Map[Local, Set[SType]]](g) {
  doAnalysis()

  override def flowThrough(a: Map[Local, Set[SType]], n: SUnit, a1: Map[Local, Set[SType]]): Unit = {
    val pta = Scene.v().getPointsToAnalysis;

    def leftPointsToSet(left: Value) : PointsToSet = {
      left match {
        case left: ArrayRef => {
          leftPointsToSet(left.getBase)
        }
        case left: InstanceFieldRef => {
          pta.reachingObjects(leftPointsToSet(left.getBase), left.getField)
        }
        case left: StaticFieldRef => {
          pta.reachingObjects(left.getField)
        }
        case left: Local => {
          pta.reachingObjects(left)
        }
      }
    }

    n match {
      case n: DefinitionStmt => {
        val pts = leftPointsToSet(n.getLeftOp)
        System.out.println(pts.possibleTypes)
      }
    }
  }

  override def merge(in1: Map[Local, Set[SType]], in2: Map[Local, Set[SType]], out: Map[Local, Set[SType]]): Unit = {
    System.out.println(out);
  }

  override def newInitialFlow(): Map[Local, Set[SType]] = new HashMap()

  override def copy(in: Map[Local, Set[SType]], out: Map[Local, Set[SType]]): Unit = {

  }

}

object ReachableTypesExtension {
  def main(args: Array[String]): Unit = {
    Options.v().set_whole_program(true)
    Options.v().setPhaseOption("cg.spark", "on")

    val jtpPack = PackManager.v().getPack("jtp")
    jtpPack.add(
      new Transform("jtp.reachableTypesTransform", new BodyTransformer() {
        def internalTransform(body: Body, phase: String, options: Map[String, String]): Unit = {
          new ReachableTypesAnalysis(new ExceptionalUnitGraph(body))
        }
      }))

    soot.Main.main(args)
  }
}
