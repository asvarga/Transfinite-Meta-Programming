
package parser

import types.*
import ordinals.*
import scala.util.parsing.combinator._
import repl.*

///

// note to self: getting loops? make sure call to method can't recurse without progress along string.
// ex: `lazy val X = X~...` may loop but `lazy val X = "("~X~...` will not.

object P extends RegexParsers: // JavaTokenParsers
  lazy val t: Parser[Term] = _c 
                           | _plus
                           | _mult
                           | _sub
                           | _ifte
                           | _app 
                           | _lam
                           | _or
                           | _or_m
                           | _plam
                           | _quo
                           | _qq
                           | _run
                           | _spl
                           | _lift
                           | _v
                           | _f
                           | _l

  def _c:    Parser[Term] = _ordinal ^^ { c(_) } // wholeNumber
  def _quo:  Parser[Term] = "'"~t ^^ { case _~t => quo(t) }
                          | "["~"'"~_mono~"]"~t ^^ { case _~_~o~_~t => quo(o, t) }
                          | "["~_mono~"]"~t ^^ { case _~o~_~t => quo(o, t) }
  def _qq:   Parser[Term] = "`"~t ^^ { case _~t => qq(t) }
                          | "["~"`"~_mono~"]"~t ^^ { case _~_~o~_~t => qq(o, t) }
  def _run:  Parser[Term] = "%"~t ^^ { case _~t => run(t) }
                          | "["~"%"~_mono~"]"~t ^^ { case _~_~o~_~t => run(o, t) }
  def _lift: Parser[Term] = "^"~t ^^ { case _~t => lift(t) }
                          | "["~"^"~_mono~"]"~t ^^ { case _~_~o~_~t => lift(o, t) }
  def _spl:  Parser[Term] = ","~t ^^ { case _~t => spl(t) }
                          | "["~","~_ord~"]"~t ^^ { case _~_~o~_~t => spl(o, t) }
  def _plus: Parser[Term] = "("~rep1(t~"+")~t~")" ^^ { case _~ts~t~_ => 
                              ts.map({case t~_ => t}).foldRight(t)(_+_) }
  def _mult: Parser[Term] = "("~rep1(t~"*")~t~")" ^^ { case _~ts~t~_ => 
                              ts.map({case t~_ => t}).foldRight(t)(_*_) }
  def _sub:  Parser[Term] = "("~t~rep1("-"~t) ~")" ^^ { case _~s~ts~_ => 
                              ts.map({case _~t => t}).fold(s)(_-_) }
  def _or:   Parser[Term] = "("~rep1(t~"||")~t~")" ^^ { case _~ts~t~_ => 
                              ts.map({case t~_ => t}).foldRight(t)(_||_) }
  def _or_m: Parser[Term] = "("~rep1(t~"|")~t~")" ^^ { case _~ts~t~_ => 
                              lam(ts.map({case t~_ => t(v())}).foldRight(t(v()))(_||_)) }
  def _ifte: Parser[Term] = "("~t~"?"~t~":"~t~")" ^^ { case _~r~_~s~_~t~_ => ifte(r,s,t) }
  def _lam:  Parser[Term] = "λ"~"."~t ^^ { case _~_~t => lam(t) }
  def _plam: Parser[Term] = "λ"~t~"~"~t ^^ { case _~p~_~t => plam(p, t) }
  def _app:  Parser[Term] = "("~t~t.* ~")" ^^ { case _~f~xs~_ => f(xs:_*) }
  def _v:    Parser[Term] = """v([1-9]\d*)""".r ^^ { case n => v(n.slice(1, n.length).toInt) }
                          | "v" ^^ { (_) => v() }
  def _f:    Parser[Term] = """f([1-9]\d*)""".r ^^ { case n => f(n.slice(1, n.length).toInt) }
                          | "f" ^^ { (_) => f() }
  def _l:    Parser[link] = """\$\w+""".r ^^ { case l => link(l.slice(1, l.length)) }

  // TODO: expand
  def _ordinal: Parser[Ordinal] = _ord | _z ^^ { _ => z() }
  def _ord:  Parser[ord]  = _mono~"<+>"~_ord ^^ { case m~_~o => (m+o).asOrd }
                          | _mono
  def _mono: Parser[ord]  = _sing~"<*>"~_pos ^^ { case s~_~n => (s*n).asOrd }
                          | _sing
  def _sing: Parser[ord]  = _w~"^"~_pos ^^ { case _~_~n => ord(n, 1, 0) }
                          | _w~"""[⁰¹²³⁴-⁹]+""".r ^^ { case _~n => ord(fromsup(n), 1, 0) }
                          | _w~"^"~"("~_ord~")" ^^ { case _~_~_~o~_ => ord(o, 1, 0) }
                          | _pos ^^ { O(_).asOrd }
                          | _w
  def _w:    Parser[ord]  = ("w"|"ω") ^^ { _ => w }
  def _nat:  Parser[Int]  =  _pos | _z
  def _pos:  Parser[Int]  =  """([1-9]\d*)""".r ^^ { _.toInt }
  def _z:    Parser[Int]  = "0" ^^ { _ => 0 }


  def apply(in: String): Term = parseAll(t, in) match {
    case Success(matched,_) => matched // println(matched)
    case Failure(msg,_) => println(s"[FAILURE(term)] $msg"); types.err()
    case Error(msg,_) => println(s"[ERROR(term)] $msg"); types.err()
  }

  ///

  def program: Parser[Program] = _command.*
  def _command: Parser[Command] = _define 
                                | _eval 
                                | _comment
                                | "("~_command~")" ^^ { case _~c~_ => c }
  def _define: Parser[Define]   = t~":="~t ^^ { case p~_~t => Define(p, t) }
  def _eval: Parser[Eval]       = t ^^ {Eval(_)}
  def _comment: Parser[Comment] = """/\\*.*\\*/""".r ^^ {Comment(_)}
                                // | "//"~t ^^ {case _~t => Comment("")}
                                // | """//.*""".r ^^ {Comment(_)} // TODO: matches ["//", _eval]

  def load(in: String): Program = parseAll(program, in) match {
    case Success(matched,_) => matched // println(matched)
    case Failure(msg,_) => println(s"[FAILURE(load)] $msg"); List(Eval(types.err()))
    case Error(msg,_) => println(s"[ERROR(load)] $msg"); List(Eval(types.err()))
  }

implicit def str2term(s: String): Term = P(s)
val load = P.load
