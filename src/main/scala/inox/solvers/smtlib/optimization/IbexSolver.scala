/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib
package optimization

import _root_.smtlib.trees.Commands._
import _root_.smtlib.trees.CommandsResponses._
import _root_.smtlib.trees.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.interpreters._
import _root_.smtlib.theories._

object optIbexQuery extends OptionDef[String] {
  import OptionParsers._
  val name = "ibex"
  val default = "ibexquery"
  val parser = stringParser
  val usageRhs = "PATH"
}

/** How close Ibex must bracket an optimum before it stops. */
object optIbexEpsF extends OptionDef[Double] {
  import OptionParsers._
  val name = "ibex-eps-f"
  val default = 1e-18
  val parser = doubleParser
  val usageRhs = "REAL"
}

/** How close, relative to the optimum, Ibex must bracket it before it stops.
  *
  * Ibex stops as soon as either this or the absolute precision is met. Its own default is
  * 1e-3, which leaves every bound up to 0.1% above the optimum.
  */
object optIbexRelEpsF extends OptionDef[Double] {
  import OptionParsers._
  val name = "ibex-rel-eps-f"
  val default = 1e-9
  val parser = doubleParser
  val usageRhs = "REAL"
}

/** How hard Ibex works to simplify an expression before searching it. */
object optIbexSimplLevel extends OptionDef[Int] {
  import OptionParsers._
  val name = "ibex-simpl-level"
  val default = 2
  val parser = intParser
  val usageRhs = "0..3"
}

class IbexInterpreter(executable: String, args: Array[String], reporter: Reporter)
  extends ProcessInterpreter(executable, args) {

  // `eval` reads one reply per command, so every command has to produce one.
  printer.printCommand(SetOption(PrintSuccess(true)), in)
  in.write("\n")
  in.flush()
  parser.parseGenResponse

  override def eval(cmd: SExpr): SExpr =
    try {
      printer.printSExpr(cmd, in)
      in.write("\n")
      in.flush()
      val res = parseResponseOf(cmd)
      drainErr()
      res
    } catch {
      case ex: Exception =>
        if (cmd == CheckSat()) CheckSatStatus(UnknownStatus)
        else Error("Solver encountered exception: " + ex)
    }

  private def drainErr(): Unit = {
    var more = err.ready()
    while (more) {
      val line = err.readLine()
      if (line eq null) more = false
      else {
        reporter.debug(line)(using DebugSectionSolver)
        more = err.ready()
      }
    }
  }
}

trait IbexTarget extends SMTLIBTarget {
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  def targetName = "ibex"

  // The server takes no arguments: it is configured over the protocol.
  protected def interpreterOpts = Seq.empty[String]

  override protected val interpreter: ProcessInterpreter = {
    val executable = options.findOptionOrDefault(optIbexQuery)
    reporter.debug(s"Invoking solver $targetName as $executable")(using DebugSectionSolver)
    new IbexInterpreter(executable, Array.empty[String], reporter)
  }

  // The server solves quantifier-free nonlinear real arithmetic
  emit(SetLogic(QF_NRA()))

  emit(SetOption(AttributeOption(Attribute(
    SKeyword("ibex-abs-eps-f"),
    Some(SDecimal(BigDecimal(options.findOptionOrDefault(optIbexEpsF))))))))

  emit(SetOption(AttributeOption(Attribute(
    SKeyword("ibex-rel-eps-f"),
    Some(SDecimal(BigDecimal(options.findOptionOrDefault(optIbexRelEpsF))))))))

  emit(SetOption(AttributeOption(Attribute(
    SKeyword("ibex-simpl-level"),
    Some(SNumeral(BigInt(options.findOptionOrDefault(optIbexSimplLevel))))))))

  /** How long the server may search before answering with what it has established so far.
    *
    * The server reads this whenever it is set, so a caller that has a budget to divide can
    * say what each query is worth instead of giving every one of them the same allowance.
    */
  def setSearchTimeout(seconds: Double): Unit =
    emit(SetOption(AttributeOption(Attribute(
      SKeyword("ibex-timeout"),
      Some(SDecimal(BigDecimal(seconds max 0.001)))))))

  private val MaxNumeral = BigInt(2).pow(53)

  override protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]): Term = e match {
    // A whole number is written plainly, because the server only folds a bound into a
    // variable's search domain in that form; as a quotient it would stay a constraint
    // and leave the domain unbounded.
    case FractionLiteral(n, d) if d == 1 => integerToTerm(n)
    case FractionLiteral(n, d) => Reals.Div(integerToTerm(n), integerToTerm(d))

    // No SMT-LIB theory names these, but the server reads them as plain applications.
    case f: RealFunction =>
      FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol(f.function))),
        f.args.map(toSMT))

    case _ => super.toSMT(e)(using bindings)
  }

  /** Writes an integer using only numerals the server accepts. */
  private def integerToTerm(n: BigInt): Term = {
    def positive(n: BigInt): Term =
      if (n <= MaxNumeral) Reals.NumeralLit(n)
      else {
        val twos = n.lowestSetBit
        if (twos >= 1) {
          val step = twos min 53
          Reals.Mul(positive(n >> step), Reals.NumeralLit(BigInt(2).pow(step)))
        } else {
          Reals.Add(
            Reals.Mul(positive(n / MaxNumeral), Reals.NumeralLit(MaxNumeral)),
            Reals.NumeralLit(n % MaxNumeral))
        }
      }

    if (n < 0) Reals.Neg(positive(-n)) else positive(n)
  }
}

trait IbexSolver extends SMTLIBSolver with IbexTarget with Solver {
  import program.trees._

  def declare(vd: ValDef): Unit = declareVariable(vd.toVariable)
}