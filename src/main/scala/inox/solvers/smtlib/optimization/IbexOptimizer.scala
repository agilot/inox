/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib
package optimization

import Commands._
import _root_.smtlib.trees.Terms._

/** An enclosure, with `None` at an end the search left open. */
case class ObjectiveBounds(lo: Option[BigDecimal], hi: Option[BigDecimal])

/** Ibex through SMT-LIB.*/
trait IbexOptimizer extends IbexSolver with AbstractOptimizer {
  import program._
  import program.trees._
  import program.symbols.{given, _}

  def assertCnstr(expr: Expr, weight: Int): Unit =
    unsupported(expr, "Ibex has no soft constraints: it brackets an optimum rather " +
      "than maximizing the weight of a satisfied subset")

  def assertCnstr(expr: Expr, weight: Int, group: String): Unit =
    assertCnstr(expr, weight)

  def minimize(expr: Expr): Unit = setObjective(expr, Minimize(_))
  def maximize(expr: Expr): Unit = setObjective(expr, Maximize(_))

  private def setObjective(expr: Expr, command: Term => SExpr): Unit = {
    exprOps.variablesOf(expr).foreach(declareVariable)
    emit(command(toSMT(expr)(using Map())))
  }

  def getObjectiveBounds: Option[ObjectiveBounds] =
    // Sent as a bare s-expression rather than as a command: the reply is a term, and
    // the generic command-response parser accepts only success/unsupported/error.
    emit(SList(List(SSymbol("get-objectives")))) match {
      case SList(List(SSymbol("objectives"), SList(SSymbol(_) :: ends))) => enclosure(ends)
      case _ => None
    }

  /** The box Ibex certified around the point it found, one enclosure per variable. */
  def getVariableBounds: Map[Variable, ObjectiveBounds] =
    emit(SList(List(SSymbol("get-info"), SKeyword("ibex-enclosure")))) match {
      case SList(List(SKeyword("ibex-enclosure"), SList(entries))) =>
        entries.flatMap {
          case SList(List(SSymbol(name), low, high)) =>
            variables.getA(SSymbol(name))
              .map(_ -> ObjectiveBounds(number(low), number(high)))
          case _ => None
        }.toMap

      // Anything else is "unsupported", or a run that proved nothing and has no box.
      case _ => Map.empty
    }

  /** Reads the two ends of an enclosure. */
  private def enclosure(ends: List[SExpr]): Option[ObjectiveBounds] =
    ends.map(number) match {
      case List(lo, hi) => Some(ObjectiveBounds(lo, hi))
      case _ => None
    }

  /** Reads one value, `None` for the `+oo` or `-oo` of an end left open. */
  private def number(e: SExpr): Option[BigDecimal] = e match {
    case SDecimal(d) => Some(d)
    case SList(List(SSymbol("-"), x)) => number(x).map(-_)
    case _ => None
  }
}

object IbexOptimizer {

  def apply(p: InoxProgram, ctx: Context): IbexOptimizer { val program: p.type } = {
    class Impl(override val program: p.type)
      extends SMTLIBSolver(p, ctx)(using p.getSemantics) with IbexOptimizer

    new Impl(p)
  }
}