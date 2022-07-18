
package trace

import types.*
import scala.collection.mutable.Stack

// Line characters from https://www.w3.org/TR/xml-entity-names/025.html

/// Tracing ///

val TAB = 2

class Tracer:
  def pre[T <: Term](t: T)(using Env): T = t
  def post[T <: Term](t: Term, v: T)(using Env): T = v
object Tracer:
  def pre[T <: Term](t: T)(using Env)(using tr: Tracer): T = tr.pre(t)
  def post[T <: Term](t: Term, v: T)(using Env)(using tr: Tracer): T = tr.post(t, v)
  def current(using tr: Tracer): Tracer = tr
  def noop: Tracer = new Tracer()
  def inputs: Tracer = new TracerInputs()
  def verbose: Tracer = new TracerVerbose()

class TracerInputs extends Tracer:
  var pre = Stack[String]()
  override def pre[T <: Term](t: T)(using Env): T =
    if (pre.length > 100) throw Exception("looping?")
    val b = if isVal(t) then ' ' else '╭'
    println(s"${pre.reverse.mkString}$b${dash*2}$t ${" "*4}⊣ ${Env.debug}") // Env.size // Env.debug // Env.level // Env.current
    pre.push(pad(pipe+t2c(t), TAB))
    t 
  override def post[T <: Term](t: Term, v: T)(using Env): T = 
    pre.pop()
    v

class TracerVerbose extends TracerInputs:
  override def post[T <: Term](t: Term, v: T)(using Env): T = 
    if !isVal(t) then
      println(s"${pre.tail.reverse.mkString}╰${dash*2}$v ${" "*4}⊣ ${Env.debug}") // Env.size // Env.debug // Env.level // Env.current
    super.post(t, v)

///

def pad(s: String, n: Int): String = s + " " * (n - s.length)
def pipe(using Env): String = if Env.isLevelZero then "│" else "┆"
def dash(using Env): String = if Env.isLevelZero then "─" else "╌"
