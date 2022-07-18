
package ordinals

import types.*
import util.*

import spire.math.Natural
import scala.math.Ordering as ScOrdering

/// Ordering ///

// TODO: use scala.math.Ordering instead
object Ordering extends Enumeration:
  type Ordering = Value
  val LT, EQ, GT = Value
import Ordering._

val inv = Map(LT -> GT, EQ -> EQ, GT -> LT)

/// Ordinals ///

sealed trait Ordinal:
  def +(that: Ordinal) = add(this, that)
  def -(that: Ordinal) = sub(this, that)
  def *(that: Ordinal) = mul(this, that)
  def /(that: Ordinal) = div(this, that)._1
  def ?(that: Ordinal) = comp(this, that)
  def <(that: Ordinal) = (this ? that) == LT
  def >(that: Ordinal) = (this ? that) == GT
  def ==(that: Ordinal) = (this ? that) == EQ
  def <=(that: Ordinal) = !(this > that)
  def >=(that: Ordinal) = !(this < that)
  def ??(that: Ordinal) = dcomp(this, that)
  def <<(that: Ordinal) = (this ?? that) == LT
  def >>(that: Ordinal) = (this ?? that) == GT
  def <>(that: Ordinal) = (this ?? that) == EQ
  def asOrd: ord = this.asInstanceOf[ord] // only use when `this` is provably ord
  override def toString: String = str(this)
case class z() extends Ordinal
case class ord(a: Ordinal, n: Natural, b: Ordinal) extends Ordinal: // assume b == 0 || a > b.a
  def +(that: ord) = add(this, that)
  def -(that: ord) = sub(this, that)
  def *(that: ord) = mul(this, that)
  def /(that: ord) = div(this, that)._1
  def ?(that: ord) = comp(this, that)
  def <(that: ord) = (this ? that) == LT
  def >(that: ord) = (this ? that) == GT
  def ==(that: ord) = (this ? that) == EQ
  def <=(that: ord) = !(this > that)
  def >=(that: ord) = !(this < that)
  def ??(that: ord) = dcomp(this, that)
  def <<(that: ord) = (this ?? that) == LT
  def >>(that: ord) = (this ?? that) == GT
  def <>(that: ord) = (this ?? that) == EQ

implicit def O(n: Natural): Ordinal = if (n == 0) then z() else ord(0, n, 0)
implicit def N(i: Int): Natural = Natural(i)
implicit def O(i: Int): Ordinal = O(N(i))
def I(n: Natural): Int = Integer(n)
val O0 = O(0)
val O1 = O(1).asOrd
val ω = ord(1, 1, 0)
val w = ω

def `ω^`(n: Ordinal): ord = if (n == O0) then O1 else ord(n, 1, 0)
val `ω²` = `ω^`(2)
val `ω³` = `ω^`(3)

/// To String ///

implicit def str(n: Natural): String = ""+n

val SUPS = "⁰¹²³⁴⁵⁶⁷⁸⁹"

def tosup(i: Natural): String = (""+i).map(_-48).map(SUPS).mkString
def fromsup(s: String): Natural = s.map(SUPS.indexOf(_)).map(""+_).mkString.toInt

def str(o: Ordinal): String = 
  def f(a: Ordinal): String = a match
    case ord(z(), 1, z()) => "ω"                // not ω^1
    case ord(z(), an, z()) => "ω"+tosup(an) // not ω^(n)
    case ord(ord(z(), 1, z()), 1, z()) => "ω^ω" // not ω^(ω)
    case _ => s"ω^(${str(a)})"
  def g(n: Natural): String = n match
    case 1 => ""                                // not ...*1
    case _ => s"*${n}"
  def h(b: Ordinal): String = b match
    case z() => ""                              // not ...+0
    case _ => s"+${str(b)}"
  o match
    case z() => "0"
    case ord(z(), n, z()) => n
    case ord(a, n, b) => f(a)+g(n)+h(b)         // ω^(a) *n +b

///

def isNat(o: Ordinal): Boolean = o match
  case z() => true
  case ord(z(), _, z()) => true
  case _ => false

def comp(x: Natural, y: Natural): Ordering = if x==y then EQ else if x<y then LT else GT

def comp(x: Ordinal, y: Ordinal): Ordering = (x, y) match
  case (z(), z()) => EQ
  case (z(), y) => LT
  case (x, z()) => GT
  case (ord(xa, xn, xb), ord(ya, yn, yb)) => comp(xa, ya) match
    case m@(LT | GT) => m
    case EQ => comp(xn, yn) match
      case m@(LT | GT) => m
      case EQ => comp(xb, yb)

def comp(x: ord, y: ord): Ordering = comp(x.a, y.a) match
  case m@(LT | GT) => m
  case EQ => comp(x.n, y.n) match
    case m@(LT | GT) => m
    case EQ => comp(x.b, y.b)

def dcomp(x: Ordinal, y: Ordinal): Ordering = (x, y) match
  case (z(), z()) => EQ
  case (z(), _) => LT
  case (_, z()) => GT
  case (ord(xa, _, _), ord(ya, _, _)) => comp(xa, ya)

def dcomp(x: ord, y: ord): Ordering = comp(x.a, y.a)

def add(x: Ordinal, y: Ordinal): Ordinal = (x, y) match
  case (x, z()) => x
  case (z(), y) => y
  case (ord(xa, xn, xb), ord(ya, yn, yb)) => comp(xa, ya) match
    case LT => y
    case GT => ord(xa, xn, add(xb, y))
    case EQ => ord(ya, xn+yn, yb)

def add(x: ord, y: ord): ord = comp(x.a, y.a) match
  case LT => y
  case GT => ord(x.a, x.n, add(x.b, y))
  case EQ => ord(y.a, x.n+y.n, y.b)

// x-y == z <=> x == y+z
def sub(x: Ordinal, y: Ordinal): Ordinal = (x, y) match
  case (x, z()) => x
  case (z(), y) => z()
  case (ord(xa, xn, xb), ord(ya, yn, yb)) => comp(xa, ya) match
    case LT => z()
    case GT => ord(xa, xn, sub(xb, y))
    case EQ => comp(xn, yn) match
      case LT => z()
      case GT => ord(xa, xn-yn, xb)
      case EQ => sub(xb, yb)

def sub(x: ord, y: ord): Ordinal = comp(x.a, y.a) match
    case LT => z()
    case GT => ord(x.a, x.n, sub(x.b, y))
    case EQ => comp(x.n, y.n) match
      case LT => z()
      case GT => ord(x.a, x.n-y.n, x.b)
      case EQ => sub(x.b, y.b)

def mul(x: Ordinal, y: Ordinal): Ordinal = (x, y) match
  case (x, z()) => z()
  case (z(), y) => z()
  case (ord(xa, xn, xb), ord(z(), yn, yb)) => ord(xa, xn*yn, xb)
  case (ord(xa, xn, xb), ord(ya, yn, z())) => ord(add(xa, ya), yn, 0)
  case (x, ord(ya, yn, yb)) => add(mul(x, ord(ya, yn, 0)), mul(x, yb))

def mul(x: ord, y: ord): ord = y match
  case ord(z(), yn, yb) => ord(x.a, x.n*yn, x.b)
  case ord(ya, yn, z()) => ord(add(x.a, ya), yn, 0)
  case ord(ya, yn, yb@ord(_, _, _)) => add(mul(x, ord(ya, yn, 0)), mul(x, yb))

// return (a, b) s.t. x = y*a + b
def div(x: Ordinal, y: Ordinal): (Ordinal, Ordinal) = (x, y) match
  case (z(), _) => (0, y)
  case (x, z()) => throw ArithmeticException("division by 0")
  case (x, ord(ord(z(), 1, z()), 1, z())) => x match
    case z() => throw Absurd  // unreachable
    case ord(z(), xn, z()) => (0, xn)
    case ord(xa, xn, xb) => {
      val (a, b) = div(xb, y)
      (ord(xa-1, xn, a), b)
    }
  case _ => throw Unimplemented // TODO:

def div(x: ord, y: ord): (Ordinal, Ordinal) = y match
  case ord(ord(z(), 1, z()), 1, z()) => x match
    case ord(z(), xn, z()) => (0, xn)
    case ord(xa, xn, xb) => {
      val (a, b) = div(xb, y)
      (ord(xa-1, xn, a), b)
    }
  case _ => throw Unimplemented // TODO:

// (w^a + ... + w^b) |-> (w^b + ... + w^a) == w^a
def _comm(x: Ordinal): Ordinal = x match
  case z() => z()
  case ord(xa, xn, _) => ord(xa, xn, 0)

object OrdinalOrdering extends ScOrdering[Ordinal] {
  def compare(a:Ordinal, b:Ordinal): Int = a ? b match
    case LT => -1
    case EQ => 0
    case GT => 1
}


/// Signed Ordinals ///

sealed trait SOrdinal:
  def unary_- = sub(this)
  def unary_+ = this
  def +(that: SOrdinal) = add(this, that)
  def -(that: SOrdinal) = sub(this, that)
  def *(that: SOrdinal) = mul(this, that)
  def ?(that: SOrdinal) = comp(this, that)
  def <(that: SOrdinal) = (this ? that) == LT
  def >(that: SOrdinal) = (this ? that) == GT
  def ==(that: Ordinal) = (this ? that) == EQ
  def <=(that: SOrdinal) = !(this > that)
  def >=(that: SOrdinal) = !(this < that)
  // def /(that: SOrdinal) = div(this, that)._1
  override def toString: String = str(this)
case class pos(o: Ordinal) extends SOrdinal
case class neg(o: Ordinal) extends SOrdinal

implicit def SO(o: Ordinal): SOrdinal = pos(o)
def O(so: SOrdinal): Ordinal = so match
  case pos(o) => o
  case neg(o) => throw Exception("negative ordinal")
implicit def SO(i: Int): SOrdinal = if i >= 0 then pos(O(i)) else neg(O(-i))

def str(so: SOrdinal): String = so match
  case pos(o) => "+"+str(o)
  case neg(o) => "-"+str(o).replace('+', '-') // FIXME: -(w^(w+1)) != -w^(w-1)

def comp(x: SOrdinal, y: SOrdinal): Ordering = (x, y) match
  case (pos(o1), pos(o2)) => comp(o1, o2)
  case (neg(o1), neg(o2)) => comp(o2, o1)
  case (pos(z()), neg(z())) => EQ
  case (neg(z()), pos(z())) => EQ
  case (pos(o1), neg(o2)) => GT
  case (neg(o1), pos(o2)) => LT

def sub(x: SOrdinal): SOrdinal = x match
  case pos(o) => neg(o)
  case neg(o) => pos(o)

def add(x: SOrdinal, y: SOrdinal): SOrdinal = (x, y) match
  case (pos(o1), pos(o2)) => pos(o1+o2)
  case (pos(o1), neg(o2)) => o1?o2 match
    case LT => neg(o2-o1)
    case EQ => 0
    case GT => pos(o1-o2)
  case (neg(o1), pos(o2)) => o1?o2 match
    case LT => pos(o2-o1)
    case EQ => 0
    case GT => neg(o1-o2)
  case (neg(o1), neg(o2)) => neg(o1+o2)

def sub(x: SOrdinal, y: SOrdinal): SOrdinal = x + -y

def mul(x: SOrdinal, y: SOrdinal): SOrdinal = (x, y) match
  case (pos(o1), pos(o2)) => pos(o1*o2)
  case (pos(o1), neg(o2)) => neg(o1*o2)
  case (neg(o1), pos(o2)) => neg(o1*o2)
  case (neg(o1), neg(o2)) => pos(o1*o2)

// def div(x: SOrdinal, y: SOrdinal): (SOrdinal, SOrdinal) = (x, y) match
