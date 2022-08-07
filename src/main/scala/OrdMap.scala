
/* 
NOTE:
- Currently, the size of each item is dependent on the size of the list (bad!)
  - this is because it stores that size as a value
- A way around this is to make size quickly computable via a walk of the list
- Give nodes flat edges to node reached by following preceding level path again
- Can also store length+end of linked list made by flat edges for quick size computation
- I think it is possible to efficiently build these flat edges
  1. annotate parens in path that should have a forward edge
  2. thread a stack of nodes through inner pad
    - for annotated parens, give flat edge to top of stack returned from recursion
- inside monomials, annotate right edges with mulitplier instead of repeating paths
  - then also annotate flat edges with difference of multipliers, yielding flat gap lists
- still have to figure out how ground level should behave
  - annotation must go on last right edge to the ground level
- at ground level, omit flat edges, have only long rights

  /\  /\  /\    /\  /\  /\  
 /  \/__\/__\  /  \/__\/__\            Example showing flat edges
/            \/            \........   Omitted at ground level

  /\    /\  
 /  3_2/__5              Example showing multiplied flat edges
/    \/____\........

--------[build path (tco)]--------->
----[follow path, build stack]----->   Right is deeper into recursion
<---[build path, destroy stack]-----

TODO:
- fix janky uses of asInstanceOf[]
- implement seek

Lessons Learned:
- distinguish lnil (overshot) vs rnil (undershot)
- For both chop/pad, use an outer loop distinct from an inner loop
  - The inner loop may use paths, while the outer should use ords
- Dependent types or something would be really useful
  - Even just being able to disinguish non-zero naturals would rule out certain cases
- Using paths isn't wasteful for pad because we'll certainly use the whole path
  - chop on the other hand might fail, and it's easy enough to use ords
- It may be possible to use ords in the inner pad by maintaining explicit stack somehow
- Handling non-monomials in pad isn't required for tfdbi
- Type checking may rule out additional cases in chop (overshoots, undershoots?)
- Revisit the possibility of using unbalanced parentheses (within monos)
*/

package ordmap

import util.*
import ordinals.*
import Ordering._

import spire.math.Natural

/// Paths ///

def ord2path(o: Ordinal): String = o match
  case z()          => ""
  case ord(a, n, b) => s"(${ord2path(a)})"*I(n)+ord2path(b)

def path2ord(path: String, stack: List[Ordinal] = List(0)): List[Ordinal] = path match
  case "" => stack
  case s"($rest" => path2ord(rest, 0 :: stack)
  case s")$rest" => stack match
    case s0 :: s1 :: s => path2ord(rest, (s1+`ω^`(s0)) :: s)
    case _ => throw Exception("whoops")

////////////////////////////////////////////////////////////////////////////////

private sealed trait OMNode[T]:
  override def toString: String = this match
    case item(l, v, _)    => s"${v.getOrElse("_")}($l"
    case pr(l, rnil())    => s"($l"
    case pr(l, r)         => s")$r" // favor right
    case _: Nil[T]        => ""
  def debug: String = this match
    case item(l, v, _)    => s"${if v.isEmpty then "_" else "t"}(${l.debug}"
    case pr(l, rnil())    => s"(${l.debug}"
    case pr(l, r)         => s")${r.debug}" // favor right
    case _: Nil[T]        => ""
  def cons(v: Option[T], size: Ordinal): item[T] = this match
    case item(l, _, _) => item(l, v, size)
    case _           => item(this.asInstanceOf[Left[T]], v, size)
  def cons(v: T, size: Ordinal): item[T] = this.cons(Some(v), size)
  def cons(size: Ordinal): item[T] = this.cons(None, size)
  def chopl = this match
    case pr(l, _)    => l
    case item(l, _, _) => l
    case _           => this
  def chopr = this match
    case pr(_, r)    => r
    case item(_, _, _) => rnil()
    case _           => this
  // assumes o is a monomial:
  def chopm(o: Ordinal): OMNode[T] = o match
    case z() => this
    case ord(a, n, b) => 
      var ret = this
      for (i <- 0 until I(n)) 
        ret = ret.chopl.chopm(a).chopr
        if ret.isInstanceOf[Nil[T]] then return ret
      ret.chopm(b)
  def padl(r: Right[T] = rnil()) = pr(this.asInstanceOf[Left[T]], r)
  def padr(l: Left[T]  = nil())  = pr(l, this.asInstanceOf[Right[T]])

sealed trait OM[T] extends OMNode[T]:
  val size: Ordinal
  val level: Ordinal
  val isLevelZero: Boolean
  def apply(o: Ordinal = 0) = this.chop(o).head
  def head: T = this match
    case item(_, Some(t), _) => t
    case _                   => throw Exception("whoops")
  def ohead: Option[T] = this match
    case item(_, Some(t), _) => Some(t)
    case _                   => None
  def cons(v: Option[T]): item[T] = this match
    case nil()            => item(nil().padr(), v, 1)
    case item(l, _, size) => item(l, v, size)
  def cons(v: T): item[T] = this.cons(Some(v))
  def cons(): item[T] = this.cons(None)
  def cons1(t: T): item[T] = this.pad(1).cons(t)
  // o may be polynomial:
  def chop(o: Ordinal): OM[T] = o match
    case z() => this
    case ord(a, n, b) => 
      var ret = this
      val mono = ord(a, 1, 0)
      for (i <- 0 until I(n)) ret.chopm(mono) match
        case rnil()        => return ret.cons()   // undershot
        case nil()         => return nil()        // overshot
        case item(l, v, s) => ret = item(l, v, s) // exact
        case t             => throw Absurd        // impossible
      ret.chop(b)
  // assumes o is a monomial:
  def pad(o: Ordinal): OM[T] = 
    def pad(t: OMNode[T], path: String): OMNode[T] = path match 
      case "" => this
      case s"($rest" => pad(t.chopl, rest).padl()
      case s")$rest" => pad(t.chopr, rest).padr(t.chopl.asInstanceOf[Left[T]])  
    pad(this, ord2path(o)).chopl.cons(o+size)
  // o may be polynomial:
  def padp(o: Ordinal): OM[T] = o match
    case z() => this
    case ord(a, n, b) => 
      var ret = this.padp(b)
      val mono = ord(a, 1, 0)
      for (i <- 0 until I(n)) ret = ret.pad(mono)
      ret
  def seek(pred: T => Boolean): OM[T] = throw Unimplemented // TODO:
  def find(pred: T => Boolean): T = this.seek(pred).head

private case class pr[T](l: Left[T], r: Right[T]) extends OMNode[T]
private case class rnil[T]() extends OMNode[T]
case class nil[T]() extends OM[T]:
  val size  = 0
  val level = 0
  val isLevelZero = true
case class item[T](l: Left[T], v: Option[T], size: Ordinal) extends OM[T]:
  val level = size / ω
  val isLevelZero = this.chopl.chopl == nil()

private type Nil[T]   = nil[T] | rnil[T]
private type Left[T]  = pr[T] | nil[T]
private type Right[T] = pr[T] | rnil[T] | item[T]

////////////////////////////////////////////////////////////////////////////////

case class DOM[T](om: OM[T], mo: OM[OM[T]]):
  override def toString: String = s"$om >< ${mo.debug}"
  def debug: String = s"${om.debug} >< ${mo.debug}"
  def size: Ordinal = om.size
  def level: Ordinal = om.level
  def isLevelZero: Boolean = om.isLevelZero
  def head: T = om.head
  def apply(o: Ordinal = 0) = this.chop(o).head
  def cons(v: Option[T]): DOM[T] = DOM(om.cons(v), mo)
  def cons(v: T): DOM[T] = DOM(om.cons(v), mo)
  def cons(): DOM[T] = DOM(om.cons(), mo)
  def cons1(t: T): DOM[T] = this.pad(1).cons(t)
  def pad(o: Ordinal): DOM[T] = 
    val mo_ = mo.chop(o)
    mo_.ohead match
      case Some(om_) => return DOM(om_, mo_)
      case None      => return DOM(om.pad(o), mo_)
    DOM(om.pad(o), mo.chop(o))
  def chop(o: Ordinal): DOM[T] = o match
    case z() => this
    case ord(a, n, b) => 
      var om_ = om
      var mo_ = mo
      val mono = ord(a, 1, 0)
      for (i <- 0 until I(n)) om_.chopm(mono) match
        case rnil()        => return DOM(om_.cons(), mo_)   // undershot
        case nil()         => return DOM(nil(), mo_)        // overshot
        case item(l, v, s) =>                               // exact
          mo_ = mo_.cons(om_).pad(mono) 
          om_ = item(l, v, s)
        case t             => throw Absurd                  // impossible
      DOM(om_, mo_).chop(b)
  def forget: DOM[T] = DOM(om, nil())


////////////////////////////////////////////////////////////////////////////////

def testOM() =
  ----()

  val L = nil().pad(1).cons("foo").pad(1).cons("bar")
  println(L)
  println(L.size)
  println(L.chop(1))
  println(L.chop(1).size)
  println(L.chop(2))
  println(L.chop(2).size)

  ----()

  val M = nil().pad(1).cons("foo").pad(w).cons("bar").pad(1).cons("baz")
  println(M)
  println(M.size)
  println(M.chop(w))
  println(M.chop(w).size)

  ----()

def testDOM() = 
  ----()
  val L: DOM[String] = DOM(nil(), nil())
  println(L)
  val L2 = L.cons1("a").pad(w).cons1("b").pad(w).cons1("c")
  println(L2)
  println(L2.chop(1))
  println(L2.chop(w))
  ----()
  println(L2)
  println(L2.chop(w).pad(w))        // remembers c()
  println(L2.chop(w).forget.pad(w)) // forgets c()
  ----()
  println(L2.chop(w+1))
  println(L2.chop(w).chop(1))
  ----()
