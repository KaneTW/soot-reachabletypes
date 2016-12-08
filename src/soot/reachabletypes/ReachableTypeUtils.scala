package soot.reachabletypes

import soot.{SootMethod, Type => SType}

import scala.collection.{mutable => m}

case class MethodArgument(thisSet: m.Set[SType], argSet: Seq[m.Set[SType]])
case class MethodResult(returnSet: m.Set[SType], thisSet: m.Set[SType], argSet: Seq[m.Set[SType]])



object ReachableTypeUtils {
  type LambdaSet = MethodArgument => MethodResult
  type AnalysisMap = m.Map[SootMethod, LambdaSet]
}
