

package ordtree


import util.*
import ordinals.*
import ordmap.*

import spire.math.Natural

////////////////////////////////////////////////////////////////////////////////

// sealed trait DoubleList[T]

// case class OrdTree[T](node: Node[T], value: T)

sealed trait Node[T]
// part of the upward trie:
case class Trie[T](l: TN[T], r: TZN[T]) extends Node[T]:
  override def toString: String = s"(${this.l}, ${this.r})"
// a zipper list (2 lists) of stacks of right nodes:
case class Zipper[T](l: List[List[Node[T]]], r: List[List[Node[T]]]) extends Node[T]:
  override def toString: String = s"${this.l.mkString("<<")}<>${this.r.mkString(">>")}"
// a leaf of the tree / root of the zipper
case class OrdTree[T](l: TN[T], v: Option[T]) extends Node[T]:
  def move(so: SOrdinal): OrdTree[T] = move_(so, this)
  override def toString: String = s"${this.v}@${this.l}"
// none
case class OTNone[T]() extends Node[T]:
  override def toString: String = "_"

type TN[T] = Trie[T] | OTNone[T]
type TZ[T] = Trie[T] | Zipper[T]
type TZN[T] = Trie[T] | Zipper[T] | OTNone[T]


def move_[T](so: SOrdinal, ot: OrdTree[T]): OrdTree[T] = so match
  case pos(ord(a, n, b)) => move_(b, move_(ord2path(ord(a, 1, 0)), I(n), ot))
  case neg(ord(a, n, b)) => move_(b, move_(ord2path(ord(a, 1, 0)), -I(n), ot))
  case _ => ot



def move_[T](p: String, i: Int, ot: OrdTree[T]): OrdTree[T] =
  // move across zipper, lazily extending
  def left[S](l: List[S], s: S, r: List[S], n: Natural, pad: S): (List[S], S, List[S]) =
    if (n == 0) (l, s, r)
    else l match
      case head :: rest => left(rest, head, s::r, n-1, pad)
      case _ => left(l, pad, s::r, n-1, pad)
  def move[S](l: List[S], s: S, r: List[S], i: Int, pad: S): (List[S], S, List[S]) =
    if (i >= 0) left(l, s, r, Natural(i), pad)
    else
      val (r_, s_, l_) = left(r, s, l, Natural(-i), pad)
      return (l_, s_, r_)


  // climb up, move over, and go back down
  def f(p: String, n: TZN[T], rstack: List[Node[T]] = Nil): (TZ[T], List[Node[T]]) = p match
    case s"($rest" => n match
      case Trie(l, r) => f(rest, l, r::rstack) match
        case (l: Trie[T], (r:TZ[T])::rstack) => (Trie(l, r), rstack)
        case (l: Trie[T], _) => (Trie(l, r), Nil)      
        case _ => throw new Exception
      case OTNone() => f(rest, n, n::rstack) match
        case (l: Trie[T], (r:TZ[T])::rstack) => (Trie(l, r), rstack)
        case (l: Trie[T], _) => (Trie(l, n), Nil)
        case _ => throw new Exception
      case _ => throw new Exception
    case s")$rest" => n match
      case Trie(l, r) => f(rest, r, rstack) match
        case (r, rstack) => (Trie(l, r), rstack)
      case n@OTNone() => f(rest, n, rstack) match
        case (r, rstack) => (Trie(n, r), rstack)
      case _ => throw new Exception
    case "" => n match
      case Zipper(l, r) => move[List[Node[T]]](l, rstack, r, i, Nil) match  // found zipper
        case (l, rstack, r) => (Zipper(l, r), rstack)
      case OTNone() => move[List[Node[T]]](Nil, rstack, Nil, i, Nil) match  // lazily create zipper
        case (l, rstack, r) => (Zipper(l, r), rstack)
      case _ => throw new Exception
    case _ => throw new Exception

  p match 
    case s"($rest" => f(rest, ot.l, OrdTree(OTNone(), ot.v)::Nil) match
      case (l: Trie[T], OrdTree(_, v)::rstack) => OrdTree(l, v)
      case (l: Trie[T], _) => OrdTree(l, None)
      case _ => throw new Exception
    case _ => throw new Exception


    
def testOrdTree() = 
  ----()
  val n = OrdTree(OTNone(), Some(5))
  println(n)
  println(n.move(1))
  println(n.move(2))
  println(n.move(3))
  println(n.move(-1))
  println(n.move(1).move(-1))
  println(n.move(w))
  println(n.move(w).move(-w))

