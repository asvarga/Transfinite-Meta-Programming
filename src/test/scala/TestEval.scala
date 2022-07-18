import org.junit.Test
import org.junit.Assert.*

import eval.*
import types.*
import ordinals.*
import trace.*
import repl.*
import parser.*

class TestEval extends TestBase:
  given Env = Env.empty
  given Lib = Lib.empty
  given Tracer = Tracer.noop  // verbose
  val repl = Repl.noop  // verbose

  def assertEval[T](s: Term, t: T): Unit =
    assertStr(eval(s), t)

  def assertEvals[T](ss: List[Term], t: T): Unit =
    for (s <- ss) assertEval(s, t)

  // @Test def test1(): Unit =
  //   val powCode = lam(2, ifte(v(),
  //                   qq(spl(v(1)) * spl(f()(v()-1))),
  //                   quo(1)  // qq(1) works too
  //                 ))
  //   assertStrs(List(
  //     "'"+repl("powCode", quo(powCode)),
  //     repl(quo(powCode)),
  //     repl(qq(powCode)),
  //   ), "'λ.λ.(v ? `(,v1*,(f (v-1))) : '1)")
    
  //   // assertStr(
  //   //   repl("power3", qq(lam("x", spl(link("powCode")(qq(v("x")), 3))))),
  //   //   "λx.v*v*v*1")
  //   assertStr(
  //     repl("power3", qq(lam(spl(link("powCode")(qq(v()), 3))))),
  //     "λ.v*v*v*1")
      
  //   assertStr(repl(link("power3")(5)), 125)

  @Test def test2(): Unit =
    val f = 
      lam(qq(
        lam(qq(
          lam(qq(
            spl(w, v()) + spl(w*2, v()) + spl(w*3, v())
          ))
        ))
      ))
    val t = run(run(run(f(qq(w*3, 30)))(qq(w*2, 20)))(qq(w, 10)))
    assertEval(t, 60)

  @Test def test3(): Unit =
    val powCodeVar = 
      lam(List("x", "y"), ifte(v("y"),
        qq(spl(v("x")) * spl(f("y")(v("y")-1))),
        qq(1)
      ))
    val powCodeInd = 
      lam(2, ifte(v(),
        qq(spl(v(1)) * spl(f()(v()-1))),
        qq(1)
      ))
    assertStr(powCodeVar, "λx.λy.(s_y(v) ? `(,s_x(v)*,(s_y(f) (s_y(v)-1))) : `1)")
    assertStrs(List(
      powCodeInd, 
      // v2i(powCodeVar),
    ), "λ.λ.(v ? `(,v1*,(f (v-1))) : `1)")

  @Test def test4(): Unit =
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
    repl("$rep_app", "λ.λ.λ.(v ? [`ω²]%([,ω²](f (v-1)) '[,ω²](($rep_q [^ω²](10*v)) (v1-v))) : v2)")
    // repl("($rep_app ($rep_lamq ($sum_s 3) 3) 3 3)") // [ω²],(,(,(λ.`λ.`λ.`(,,,v+,,v+,v) '''10) ''20) '30)

    repl("$f", "λ.($rep_app ($rep_lamq ($sum_s v) v) v v)")
    // repl("($f 3)")                    // [ω²],(,(,(λ.`λ.`λ.`(,,,v+,,v+,v) '''10) ''20) '30)
    assertStr(repl("[%ω²]($f 3)"), 60)

  @Test def test6(): Unit =
    val t = lift(C(111)+C(222))
    assertEval(t, "'333")
