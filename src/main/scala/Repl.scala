
package repl

import eval.*
import trace.*
import types.*

///

class Repl:
  given Env = Env.empty
  given Lib = Lib.empty

  // def define(s: Sym, t: Term)(using Tracer): Term = 
  //   val code = Code(evalZ(t)); Lib.current += s -> code; code.t
  def define(p: Term, t: Term)(using Tracer): Term = 
    val code = evalZ(t)
    mtch(p, code) match
      case None => throw new Exception("pattern mismatch")
      case Some(m) => 
        // println(m)
        for ((p, t) <- m) p match
          case link(s) => Lib.current += s -> t
          case _ => ()
    code
  def eval(t: Term)(using Tracer): Val = evalZ(t)
  def get(s: Sym): Term = Lib(s)

  // def apply(s: Sym, t: Term)(using Tracer): Term = define(s, t)
  def apply(p: Term, t: Term)(using Tracer) = define(p, t)
  def apply(t: Term)(using Tracer) = eval(t)
  def apply(p: Program)(using Tracer) = 
    for (c <- p) 
      println(s"// $c")
      c match 
        case Define(s, t) => define(s, t)
        case Eval(t) => eval(t)
        case Comment(s) => {}


class ReplVerbose extends Repl:
  // override def define(s: Sym, t: Term)(using Tracer): Term = 
  //   val code = Code(evalZ(t)); Lib.current += s -> code; log(code.t)
  override def define(p: Term, t: Term)(using Tracer): Term = 
    log(super.define(p, t))
  override def eval(t: Term)(using Tracer): Val = log(evalZ(t))
  // override def apply(s: Sym, t: Term)(using Tracer) = 
  //   println(s"let '$s :="); define(s, t)
  override def apply(p: Term, t: Term)(using Tracer) = 
    println(s"let $p :="); define(p, t)

object Repl:
  def noop: Repl = new Repl()
  def verbose: Repl = new ReplVerbose()

///

sealed trait Command
case class Define(p: Term, t: Term) extends Command:
  override def toString: String = s"$p := $t"
case class Eval(t: Term) extends Command:
  override def toString: String = t //s"eval $t"
case class Comment(s: String) extends Command:
  override def toString: String = s

type Program = List[Command]
