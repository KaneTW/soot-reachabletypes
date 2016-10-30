import java.util
import java.util._
import java.util.function.{BiConsumer, BiFunction, Consumer}

import soot.jimple._
import soot.options.Options
import soot.{Body, BodyTransformer, Local, PackManager, PointsToSet, Scene, Transform, Value, Type => SType, Unit => SUnit}
import soot.toolkits.graph.{DirectedGraph, ExceptionalUnitGraph}
import soot.toolkits.scalar.ForwardFlowAnalysis

// refactor into trait later
class ReachableTypesAnalysis(g: DirectedGraph[SUnit]) extends ForwardFlowAnalysis[SUnit, Map[Value, Set[SType]]](g) {
  doAnalysis()

  override def flowThrough(before: Map[Value, Set[SType]], n: SUnit, after: Map[Value, Set[SType]]): Unit = {
    val pta = Scene.v().getPointsToAnalysis
    copy(before, after)

    def leftBase(left: Value): Value = left match {
      case left: ArrayRef => // xs[n] => xs
        leftBase(left.getBase)
      case left: InstanceFieldRef => // xs.foo => xs
        leftBase(left.getBase)
      case left: StaticFieldRef => // Class.foo
        left
      case left: Local => // xs
        left
      case _ =>
        throw new RuntimeException("Unknown left operator " + left.getType)
    }

    def possibleTypesOf(v: Value): Set[SType] = v match {
      case v: Local =>
        before.getOrDefault(v, pta.reachingObjects(v).possibleTypes())
      case v: StaticFieldRef =>
        before.getOrDefault(v, pta.reachingObjects(v.getField).possibleTypes())
      case v: InstanceFieldRef =>
        v.getBase match {
          case base: Local =>
            before.getOrDefault(base, pta.reachingObjects(base, v.getField).possibleTypes())
          case _ => throw new RuntimeException("Expected Local base for InstanceFieldRef")
        }
      case v: ArrayRef =>
        possibleTypesOf(v.getBase)

      case _ => new HashSet[SType](Collections.singleton(v.getType))
    }

    n match {
      case n: DefinitionStmt =>
        val left = n.getLeftOp
        val right = n.getRightOp
        val base = leftBase(left)

        val rightTypes = possibleTypesOf(right)

        after.merge(base, rightTypes,
          new BiFunction[Set[SType], Set[SType], Set[SType]] {
            override def apply(t: util.Set[SType], u: util.Set[SType]) = {
              t.addAll(u)
              t
            }
          })

      case _ =>
    }
  }

  override def merge(in1: Map[Value, Set[SType]], in2: Map[Value, Set[SType]], out: Map[Value, Set[SType]]): Unit = {
    out.putAll(in1)
    in2.forEach(new BiConsumer[Value, Set[SType]] {
      override def accept(t: Value, u: util.Set[SType]) = {
        out.merge(t, u, new BiFunction[Set[SType], Set[SType], Set[SType]] {
          override def apply(s1: util.Set[SType], s2: util.Set[SType]) = {
            val s3 = new util.HashSet[SType]()
            s3.addAll(s1)
            s3.addAll(s2)
            s3
          }
        })
      }
    })
  }

  override def newInitialFlow(): Map[Value, Set[SType]] = new HashMap()

  override def copy(in: Map[Value, Set[SType]], out: Map[Value, Set[SType]]): Unit = {
    out.putAll(in)
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
          val ana = new ReachableTypesAnalysis(new ExceptionalUnitGraph(body))
          System.out.println(body)
          System.out.println(ana.getFlowAfter(body.getUnits.getLast))
        }
      }))

    soot.Main.main(args)
  }
}
