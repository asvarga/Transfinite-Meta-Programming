

package ordtree


import util.*
import ordinals.*
import ordmap.*

import spire.math.Natural

////////////////////////////////////////////////////////////////////////////////

// sealed trait DoubleList[T]

// case class OrdTree[T](node: Node[T], value: T)

sealed trait Node[T]:
  def map[S](f: T => S): Node[S]
// part of the upward trie:
case class Trie[T](l: TN[T] = OTNone[T](), r: TZN[T] = OTNone[T]()) extends Node[T]:
  // override def toString: String = s"(${l}, ${r})"
  def map[S](f: T => S): Trie[S] = Trie(mapTN(l, f), mapTZN(r, f))
// a zipper list (2 lists) of stacks of right nodes:
case class Zipper[T](l: List[List[Node[T]]] = Nil, r: List[List[Node[T]]] = Nil) extends Node[T]:
  // override def toString: String = 
    // s"${l.map(L => L.mkString("[",",","]")).mkString("<<")}<>${r.map(L => L.mkString("[",",","]")).mkString(">>")}"
  def map[S](f: T => S): Zipper[S] = Zipper(l.map(_.map(_.map(f))), r.map(_.map(_.map(f))))
// a leaf of the tree / root of the zipper
case class OrdTree[T](l: TN[T] = OTNone[T](), v: Option[T] = None) extends Node[T]:
  def move(so: SOrdinal): OrdTree[T] = move_(so, this)
  def set[S](t: T): OrdTree[T] = OrdTree(l, Some(t))
  // override def toString: String = s"${v}@${l}"
  def map[S](f: T => S): OrdTree[S] = OrdTree(mapTN(l, f), v.map(f))
// none
case class OTNone[T]() extends Node[T]:
  // override def toString: String = "_"
  def map[S](f: T => S): OTNone[S] = OTNone()

type TN[T] = Trie[T] | OTNone[T]
def mapTN[T, S](n: TN[T], f: T => S): TN[S] = n match {case n@Trie(_, _) => n.map(f); case _ => OTNone()}
type TZ[T] = Trie[T] | Zipper[T]
def mapTZ[T, S](n: TZ[T], f: T => S): TZ[S] = n match {case n@Trie(_, _) => n.map(f); case n@Zipper(_, _) => n.map(f)}
type TZN[T] = Trie[T] | Zipper[T] | OTNone[T]
def mapTZN[T, S](n: TZN[T], f: T => S): TZN[S] = n match {case n@Trie(_, _) => n.map(f); case n@Zipper(_, _) => n.map(f); case _ => OTNone()}


def move_[T](so: SOrdinal, ot: OrdTree[T]): OrdTree[T] = so match
  case pos(ord(a, n, z())) => move_(ord2path(ord(a, 1, 0)), I(n), ot)
  case neg(ord(a, n, z())) => move_(ord2path(ord(a, 1, 0)), -I(n), ot)
  // case pos(z()) | neg(z()) => ot
  case _ => throw new Exception



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
        case (l: Trie[T], (r:TZN[T])::rstack) => (Trie(l, r), rstack)
        case (l: Trie[T], Nil) => (Trie(l, r), Nil)      
        case _ => throw new Exception
      case OTNone() => f(rest, n, n::rstack) match
        case (l: Trie[T], (r:TZN[T])::rstack) => (Trie(l, r), rstack)
        case (l: Trie[T], Nil) => (Trie(l, n), Nil)
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
  // val n = OrdTree(OTNone(), Some(5))
  // println(n)
  // println(n.move(1))
  // println(n.move(2))
  // println(n.move(3))
  // println(n.move(-1))
  // println(n.move(1).move(-1))
  // println(n.move(w))
  // println(n.move(w).move(-w))
  // val n  = OrdTree[Int]()
  // println(n)
  // println(n.set(5).v)
  // println(n.set(5).move(1).set(6).v)
  // println(n.set(5).move(1).set(6).move(w).set(7).v)
  // println(n.set(5).move(1).set(6).move(w).set(7).move(-w).v)
  // println(n.set(5).move(1).set(6).move(w).set(7).move(-w).move(-1).v)
  // println()
  // println(n.set(5).move(1).set(6).move(w).set(7).move(-1).set(8).v)
  // println(n.set(5).move(1).set(6).move(w).set(7).move(-1).set(8).move(-w).move(-1).v)
  // println(n.set(5).move(1).set(6).move(w).set(7).move(-1).set(8).move(-w).move(-1).move(w).v)
  // println(n.set(5).move(1).set(6).move(w).set(7).move(-1).set(8).move(-w).move(-1).move(w).move(1))
  // println(n.set(5).move(1).set(6).move(w).set(7).move(-1).set(8).move(-w).move(-1).move(w).move(1).map(_+1))
  // println(n.set(5).move(1).set(6).move(w).set(7)
  //   .move(`ω^`(w)).move(-`ω^`(w))
  //   .move(-1).set(8).move(-w).move(-1).move(w).move(1).v)

  val n2 = OrdTree[String]()
  val ww = `ω^`(w)
  val www = `ω^`(ww)
  // draw(n2.set("A").move(w).set("B").move(1).set("C"))
  // draw(n2.set("A").move(1).set("B").move(w).set("C"))
  // draw(n2.set("A").move(w).set("B").move(w*w).set("C").move(w*w*w).set("D").move(ww).set("E"))
  draw(n2.set("A").move(w).set("B").move(w*w).set("C").move(ww).set("E"))
  // draw(n2.set("A").move(w).set("B").move(1).set("C").move(ww).set("E"))


// neato out/*.dot -n -Tpng -O
def draw(n: OrdTree[String]) =

  case class Point(s: String = "", x: Int = 0, y: Int = 0, z: Int = 0)

  import java.io._
  val pw = new PrintWriter(new File("local/Z.dot" ))
  def line(x: String) = 
    pw.write(x + "\n")
  line("digraph G {")
  line("  splines=true;")
  line("  node [shape=circle, style=filled, label=\"\"];")

  var _id = 0
  def id() = {_id += 1; _id}

  def point(x: Int = 0, y: Int = 0, z: Int = 0, label: String = "", color: String = "white"): Point = 
    val name = s"n_${id()}"
    line(s"  $name [pos=\"${x*50-z*25},${y*50}!\", label=\"$label\", fillcolor=$color];")
    // line(s"  $name [pos=\"${y*50},${z*50}!\", label=\"$label\", fillcolor=$color];")    // rotated for now
    // line(s"  $name [pos=\"${-z*50},${y*50}!\", label=\"$label\", fillcolor=$color];")    // rotated for now
    return Point(name, x, y, z)

  def edge(x: Point, y: Point) = 
    line(s"  ${x.s} -> ${y.s};")
    x
    

  var _xmax = 0
  def xmax() = {_xmax += 1; _xmax}
  var _xmin = 0
  def xmin() = {_xmin -= 1; _xmin}
  var _ymin = 0
  def ymin() = {_ymin -= 2; _ymin}


    
  def f(n: Node[String]): Option[Point] =
    val hash = n.hashCode()
    println(s"$hash\t<- $n")
    val ret = n match
      case OrdTree(l, v) => 
        val label = v.getOrElse("")
        val color = "orange"
        f(l) match
          case Some(pl) => Some(edge(point(0, pl.y-1, pl.z-1, label=label, color=color), pl))
          case None => Some(point(0, ymin(), 0, label=label, color=color))
      case OTNone() => None
      case Zipper(l, r) => Some(point(0, ymin(), 0, color="pink"))
      case Trie(l, r) => 
        val color = "teal"
        // go left first but priotritize right for placement
        val pl = f(l)
        f(r) match
          case Some(pr) => 
            val p = edge(point(0, pr.y-1, pr.z+1, color=color), pr)
            pl match
              case Some(pl) => Some(edge(p, pl))
              case None => Some(p)
          case None =>
            pl match
              case Some(pl) => Some(edge(point(0, pl.y-1, pl.z-1, color=color), pl))
              case None => None
        
    println(s"$hash\t-> $ret")
    ret
    

    // n.l match
    // case OrdTree(OTNone(), v) => 
    //   val x = xmax()
    //   val y = ymax()
    //   val name = node(x, y, 0, v.getOrElse(""), "red")
      // edge(node(label=n.v.getOrElse("")), node(0, 1, 1, color="red"))
    // val y = 0
    // def findYs(n: OrdTree[String]): List[Int] = n match
    //   case OrdTree(OTNone(), _) => Nil
    //   case OrdTree(Trie(l, r), _) => findYs(l) ++ findYs(r)
    // edge(point(label=n.v.getOrElse("")), point(0, 1, 1, color="red"))

  // def 

  f(n)
  line("}")
  pw.close
  



/*
TODO:
  - test
  - use in interpreter as env
  - write it up

*/