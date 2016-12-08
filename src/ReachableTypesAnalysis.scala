
import java.util

import soot.cg.utils.CallGraphUtils._
import soot.reachabletypes._
import soot.reachabletypes.ReachableTypeUtils._
import soot.heapshape.HeapShapeAnalysis
import soot.jimple._
import soot.options.Options
import soot.toolkits.graph.{DirectedGraph, ExceptionalUnitGraph}
import soot.toolkits.scalar.ForwardFlowAnalysis
import soot.{Body, BodyTransformer, Local, MethodOrMethodContext, PackManager, Scene, SceneTransformer, SootMethod, Transform, Value, Type => SType, Unit => SUnit}

import scala.collection.JavaConverters._
import scala.collection.{immutable => im, mutable => m}



// refactor into trait later
class ReachableTypesAnalysis(heapShapeAnalysis: HeapShapeAnalysis, anaMap: AnalysisMap, sootMethod: SootMethod, methodArgs: MethodArgument) extends ForwardFlowAnalysis[SUnit, m.Map[Value, m.Set[SType]]](new ExceptionalUnitGraph(sootMethod.getActiveBody)) {
  doAnalysis()

  def getResultsAfter(n: SUnit) = {
    val flow = getFlowAfter(n)

    val thisRef = flow.getOrElse(sootMethod.getActiveBody.getThisLocal, m.HashSet())
    val argRef = sootMethod.getActiveBody.getParameterLocals.asScala.map{v => flow.getOrElse(v, m.HashSet())}

    n match {
      case n: ReturnStmt =>
        MethodResult(flow(n.getOp), thisRef, argRef)
      case _ =>
        MethodResult(m.HashSet(), thisRef, argRef)
    }
  }

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

      case v: InstanceInvokeExpr =>
        val res = anaMap(v.getMethod)(MethodArgument(possibleTypesOf(v.getBase), v.getArgs.asScala.map(possibleTypesOf).seq))
        updateAfter(res.thisSet)(v.getBase)
        res.argSet.zip(v.getArgs.asScala.seq).foreach{case (s,v) => updateAfter(s)(v)}
        res.returnSet
      case v: StaticInvokeExpr =>
        val res = anaMap(v.getMethod)(MethodArgument(null, v.getArgs.asScala.map(possibleTypesOf).seq))
        res.argSet.zip(v.getArgs.asScala.seq).foreach{case (s,v) => updateAfter(s)(v)}
        res.returnSet

      case v: ThisRef =>
        before.getOrElse(v, methodArgs.thisSet)

      case v: ParameterRef =>
        before.getOrElse(v, methodArgs.argSet(v.getIndex))

      case _ => m.HashSet(v.getType)
    }

    def updateAfter(newSet: m.Set[SType])(left: Value) : Unit = {
      val old = after.getOrElse(left, m.Set())
      after.put(left, old ++ newSet)
      heapShapeAnalysis.getPredecessors(sootMethod, n, left).foreach(updateAfter(newSet))
    }

    n match {
      case n: DefinitionStmt =>
        val left = n.getLeftOp
        val rightTypes = possibleTypesOf(n.getRightOp)
        updateAfter(rightTypes)(left)

      case n: InvokeStmt =>
        possibleTypesOf(n.getInvokeExpr)

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

    val wjtpPack = PackManager.v().getPack("wjtp")

    wjtpPack.add(
      new Transform("wjtp.reachableTypesTransform", new SceneTransformer() {
        def internalTransform(phase: String, options: util.Map[String, String]): Unit = {
          val cg = Scene.v().getCallGraph.asDirectedGraph

          val anaMap = m.Map[SootMethod, LambdaSet]().withDefault{
            sm =>
              // default for unanalyzed functions
              { margs =>
                val thisType: m.Set[SType] = if (sm.isStatic) m.HashSet() else { m.HashSet(sm.getDeclaringClass.getType) }
                MethodResult(m.HashSet(sm.getReturnType), thisType, sm.getParameterTypes.asScala.seq.map(m.HashSet(_)))
              }

          }

          val sinks = cg.getTails.asScala.filter{ sm => Scene.v().getApplicationClasses.contains(sm.getDeclaringClass) }

          class DummyHeapShape extends HeapShapeAnalysis {
            override def getPredecessors(method: SootMethod, unit: SUnit, ref: Value) = Set()
          }

          def visitMethod(mc: MethodOrMethodContext): Unit = {
            val sm = mc.method()
            if (!anaMap.contains(sm)) {
              anaMap(sm) = { margs =>
                val ana = new ReachableTypesAnalysis(new DummyHeapShape(), anaMap, sm, margs)
                ana.getResultsAfter(sm.getActiveBody.getUnits.getLast)
              }
            }
            cg.getPredsOf(sm).asScala.foreach(visitMethod)
          }
          sinks.foreach(visitMethod)
          Console.println(anaMap(cg.getHeads.get(0))(MethodArgument(null, Seq(m.Set()))))
        }
      }))

    soot.Main.main(args)
  }
}

