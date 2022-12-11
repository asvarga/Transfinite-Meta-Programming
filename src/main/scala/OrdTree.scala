

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
case class Trie[T](l: TN[T], r: TZN[T]) extends Node[T]
// a zipper list (2 lists) of stacks of right nodes:
case class Zipper[T](l: List[List[Node[T]]], r: List[List[Node[T]]]) extends Node[T]
// a leaf of the tree / root of the zipper
case class OrdTree[T](l: TN[T], v: Option[T]) extends Node[T]
// none
case class OTNone[T]() extends Node[T]

type TN[T] = Trie[T] | OTNone[T]
type TZ[T] = Trie[T] | Zipper[T]
type TZN[T] = Trie[T] | Zipper[T] | OTNone[T]


def move[T](ot: OrdTree[T], o: Ordinal): OrdTree[T] = o match
  case z() => ot
  case ord(a, n, b) => move(move(ord2path(a), I(n), ot), b)

// def move[T](p: String, i: Int, ot: OrdTree[T]): OrdTree[T] =
//   // climb up the tree by following trie
//   def up(p: String, n: TZN[T], rstack: List[Node[T]]): (Zipper[T], List[Node[T]]) = p match
//     case "" => n match
//       case Trie(_, _) => throw new Exception
//       case Zipper(_, _) => (n, rstack)           // found zipper
//       case OTNone() => (Zipper([], []), rstack)  // lazily create new zipper
//     case s"($rest" => n match
//       case Trie(l, r) => up(rest, l, r::rstack)  // push r onto rstack
//       case Zipper(_, _) => throw new Exception
//       case OTNone() => up(rest, n, rstack)
//     case s")$rest" => n match
//       case Trie(_, r) => up(rest, r, rstack)
//       case Zipper(_, _) => throw new Exception
//       case OTNone() => up(rest, n, rstack)
//   val (zipper, rstack) = up(p, ot.l, [ot])

//   // move across zipper, lazily extending
//   def left[S](l: List[S], s: S, r: List[S], n: Natural, pad: S): (List[S], S, List[S]) =
//     if (n == 0) (l, s, r)
//     else l match
//       case head :: rest => left(rest, head, s::r, n-1, pad)
//       case _ => left(l, pad, s::r, n-1, pad)
//   def move[S](l: List[S], s: S, r: List[S], i: Int, pad: S): (List[S], S, List[S]) =
//     if (i >= 0) left(l, s, r, i, pad)
//     else {
//       val (r, s, l) = left(r, s, l, -i, pad)
//       (l, s, r)
//     }
//   val (l, s, r) = move[List[Node[T]]](zipper.l, rstack, zipper.r, i, [])

//   // descend back down tree
//   def down(p: String, n: TZN[T], rstack: List[Node[T]]): OrdTree[T] = p match
//     case "" => n
//     case s"$rest(" => rstack match
//       case OrdTree(_, v) :: tail => OrdTree(n, v)
//       case r :: tail => down(rest, Trie(n, r))
//       case [] => throw new Exception    // FIXME: actually lazily build down
//     case s"$rest)" => down(rest, Trie(?, n), rstack)  // TODO: 
//   return down(p, Zipper(l, r), s)

def move[T](p: String, i: Int, ot: OrdTree[T]): OrdTree[T] =
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
        case (l: Trie[T], Nil) => (Trie(l, r), Nil)      
        case _ => throw new Exception
      case OTNone() => f(rest, n, n::rstack) match
        case (l: Trie[T], (r:TZ[T])::rstack) => (Trie(l, r), rstack)
        case (l: Trie[T], Nil) => (Trie(l, n), Nil)
        case _ => throw new Exception
      case _ => throw new Exception
    case s")$rest" => n match
      case Trie(l, r) => f(rest, r, rstack) match
        case (r: Trie[T], rstack) => (Trie(l, r), rstack)
        case _ => throw new Exception
      case n@OTNone() => f(rest, n, rstack) match
        case (r: Trie[T], rstack) => (Trie(n, r), rstack)
        case _ => throw new Exception
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
      case _ => throw new Exception
    case _ => throw new Exception


    
def testOrdTree() = 
  ----()


