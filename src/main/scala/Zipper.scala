


package zipper

import util.*
import ordinals.*
import ordmap.*
import Ordering._

////////////////////////////////////////////////////////////////////////////////

// NOTE: we can declare methods in the sealed traits and specialize their types in the case classes


private sealed trait Node[T]:
  override def toString: String = this match
    case nil()           => "."
    case pair(nil(), r)  => s")$r"
    case pair(l, r)       => s"($l"
    case dn(nil(), r, v) => s"$v."
    case dn(l, r, v)      => s"$v($l"
    case up(nil(), r, v) => s"$v."
    case up(l, r, v)      => s"$v($l"
  def isNil: Boolean = this.isInstanceOf[nil[T]] // this == nil()
  def getL: Pair[T] = this match
    case pair(l, _) => l
    case dn(l, _, _) => l
    case up(l, _, _) => l
    case _ => nil()
  def getR: Node[T] = this match
    case pair(_, r) => r
    case _ => nil()
  def pairL(r: Node[T] = nil()) = pair(this.asInstanceOf[Pair[T]], r)
  def pairR(l: Pair[T] = nil()) = pair(l, this)


sealed trait Zip[T] extends Node[T]:
  def cons(v: T): Zip[T]
  def pad(o: Ordinal, v: T): Zip[T]
// sealed trait Pair[T] extends Node[T]

// type Node[T] = pair[T] | dn[T] | up[T] | nil[T]
// type Zip[T] = dn[T] | up[T]
private type Pair[T] = pair[T] | nil[T]
// private type Nil[T] = nil[T] | nil[T]
private type Up[T] = up[T] | nil[T]
private type Dn[T] = dn[T] | nil[T]
private type Pud[T] = pair[T] | up[T] | dn[T]


private case class pair[T](l: Pair[T], r: Node[T]) extends Node[T] // Pair[T]
private case class nil[T]() extends Node[T] // Pair[T]
// private case class nil[T]() extends Node[T]
private case class dn[T](l: Pair[T], eq: Up[T], v: T) extends Zip[T]:
  def cons(v: T): dn[T] = dn(this.l, this.eq, v)
  // def pad(o: Ordinal): dn[T] = this
  def pad(o: Ordinal, v: T): dn[T] = 
    def pad(t: Node[T], path: String): Pud[T] = path match 
      case "" => this
      case s"($rest" => pad(t.getL, rest).pairL()
      case s")$rest" => pad(t.getR, rest).pairR(t.getL)  
    dn(pad(this, ord2path(o)).getL, nil(), v)

private case class up[T](l: Pair[T], eq: Dn[T], v: T) extends Zip[T]:
  def cons(v: T): up[T] = up(this.l, this.eq, v)
  def pad(o: Ordinal, v: T): up[T] = this

// type ZipO[T] = Zip[Option[T]]

// def NIL[T]: nil[T] = nil()
def empty[T]():     dn[Option[T]] = dn(nil(), nil(), None)
def empty[T](v: T): dn[Option[T]] = dn(nil(), nil(), Some(v))

////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////


def testZipper() = 
  ----()
  // println("zip!")
  val t = empty()//.cons(Some(5))
  println(t)
  val s = t.pad(w*w, None)
  println(s)
  ----()
