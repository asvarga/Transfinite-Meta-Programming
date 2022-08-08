
import ordmap.*
import eval.*
import ordinals.*
import trace.*
import repl.*
import types.*
import util.*
import parser.*

/// Main ///

@main def hello: Unit =
  given DEnv = DEnv.empty
  given Tracer = Tracer.verbose
  
  // test4()
  // testOM()
  // test7()
  test8()
  // testDOM()
  // test9()
  // test10()
  // test11()

def test10() = 
  ----()
  val m = mtch("`λ.(,v + ,v1 + ,$q + ,$_)", "'λ.(3 + 4 + 5 + 6)")
  println(m)
  ----()
  
def test4()(using DEnv, Tracer) =
  given Lib = Lib.empty
  val repl = Repl.noop
  ----()

  repl("$rep_qq", "λ.λ.(v ? [`ω²]`[,ω²](f (v-1)) : v1)")
  repl("$rep_q",  "λ.λ.(v ? [`ω²]'[,ω²](f (v-1)) : v1)")
  repl("$rep_s",  "λ.λ.(v ? [`ω²],[,ω²](f (v-1)) : v1)")
  // repl("($rep_qq [ω²]123 3)")       // [ω²]```123
  // repl("($rep_q  [ω²]123 3)")       // [ω²]'''123
  // repl("($rep_s  [ω²]123 3)")       // [ω²],,,123

  repl("$sum_s", "λ.((v-1) ? [`ω²]([,ω²](($rep_s [`ω²]v) v)+[,ω²](f (v-1))) : [`ω²],v)")
  // repl("($sum_s 3)")                // [ω²](,,,v+,,v+,v)
  repl("$rep_lamq", "λ.λ.(v ? [`ω²]λ.`[,ω²](f (v-1)) : v1)")
  // repl("($rep_lamq ($sum_s 3) 3)") // [ω²]λ.`λ.`λ.`(,,,v+,,v+,v)
  repl("$rep_app", "λ.λ.λ.(v ? [`ω²],([,ω²](f (v-1)) '[,ω²](($rep_q [^ω²](10*v)) (v1-v))) : v2)")
  // repl("($rep_app ($rep_lamq ($sum_s 3) 3) 3 3)") // [ω²],(,(,(λ.`λ.`λ.`(,,,v+,,v+,v) '''10) ''20) '30)

  repl("$f", "λ.($rep_app ($rep_lamq ($sum_s v) v) v v)")
  // repl("($f 3)")                    // [ω²],(,(,(λ.`λ.`λ.`(,,,v+,,v+,v) '''10) ''20) '30)
  repl("[,ω²]($f 3)")                  // 60

  ----()

def test7()(using DEnv, Tracer) =
  given Lib = Lib.empty

  ----()
  val plus = lam(lam(v()+v(1)))
  eval(app(plus, 3, 4))
  ----()
  val plusA = lamA(lamA(v(0)+v(1)))
  eval(appA(plusA, 3, 4))
  ----()
  val plusB = lamB(lamB(v(1)+v(2)))
  eval(appB(plusB, 3, 4))
  ----()
  val double = lam(v(0)+v(0))
  eval(app(double, 5))
  ----()
  val doubleA = lamA(v(0)+v(0))
  eval(appA(doubleA, 5))
  ----()
  val doubleB = lamB(v(1)+v(1))
  eval(appB(doubleB, 5))
  ----()

def test8()(using Tracer) =
  import scala.io.Source._

  val repl = Repl.noop
  ----()
  // val code = fromFile("examples/ex3.tfdbi").getLines.mkString("\n")
  // val code = fromFile("examples/unstage.tfdbi").getLines.mkString("\n")
  val code = fromFile("examples/retentive.tfdbi").getLines.mkString("\n")
  val prog: Program = load(code)
  // println(code)
  // println(prog)
  // prog.map(println)
  repl(prog)
  ----()

def test9()(using DEnv, Tracer) =
  given Lib = Lib.empty
  // val repl = Repl.noop
  ----()
  val plus = lam(lam(v()+v(1)))
  eval(app(plus, 3, 4))
  ----()


def test11()(using DEnv, Tracer) =
  given Lib = Lib.empty
  // val repl = Repl.noop
  ----()
  val t: Term = "(λ.`(λ.,`(,v + v)))"
  println(t)

