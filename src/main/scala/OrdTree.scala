

package ordtree


import util.*
import ordinals.*
import ordmap.*

import collection.mutable
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
        case (l: Trie[T], Nil) => (Trie(l, OTNone()), Nil)      
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

  
  val ww = `ω^`(w)
  val www = `ω^`(ww)

  val n2 = OrdTree[String]()
    // .set("A")
    // .set("A").move(1).set("B").move(w).set("C").move(-1).set("D").move(ww).set("E")
    .move(-w)//.set("B")//.move(-w).set("B")
    .move(-1)//.set("Z")//.move(-1).set("Z")
    .move(ww)//.set("C")//.move(ww).set("C")
    .move(-w*w)//.set("D")//.move(-w*w).set("D")
    .move(w)//.set("E")//.move(w).set("E")
    .move(-1)//.set("F")//.move(-1).set("F")
    .move(-1)//.set("G")//.move(-1).set("G")
    // .move(w*w
    .move(1)//.move(1)
    // .move(-ww)
    // .move(-1)
    // .move(-w)
    // .move(-1)
    // .move(-w*w)
    // .move(-w)
    // .move(-1)
    // .move(-www)
    // .move(-w*w*w)
    

  draw(n2)
  // draw(n2.set("A").move(w).set("B").move(1).set("C"))
  // draw(n2.set("A").move(1).set("B").move(w).set("C"))
  // draw(n2.set("A").move(w).set("B").move(w*w).set("C").move(w*w*w).set("D").move(ww).set("E"))
  // draw(n2.set("A").move(ww).set("B").move(-w*w).set("C").move(w).set("E"))
  // draw(n2.set("A").move(w).set("B").move(1).set("C").move(ww).set("E"))
  // println(n2.set("A").move(1).set("B").move(w).set("C").move(-1).v)


// neato out/*.dot -n -Tpng -O
def draw(n: OrdTree[String]) =

  val WHITE = "#E0FBFC"
  val GREEN = "#59B36E"
  val BLUE = "#2E86AB"
  val ORANGE = "#EF7B45"
  val LIGHT_PINK = "#D87CAC"
  val DARK_PINK = "#BD4089"


  case class Point(s: String = "", x: Int = 0, y: Int = 0, z: Int = 0)

  import java.io._
  val pw = new PrintWriter(new File("local/Z.dot" ))
  def line(x: String) = 
    pw.write(x + "\n")
  line("digraph G {")
  line(s"  bgcolor=\"$WHITE\"")
  line("  node [shape=circle, style=filled, label=\"\"];")
  line("  edge [arrowsize=0.8];")
  // line("  splines=true;")
  line("  outputorder=\"edgesfirst\";")
  // line("  outputorder=\"nodesfirst\";")

  var _id = 0
  def id() = {_id += 1; _id}

  def point(x: Int = 0, y: Int = 0, z: Int = 0, label: String = "", color: String = "white", shape: String = "circle", orientation: Int = 0): Point = 
    val name = s"n_${id()}"
    line(s"  $name [pos=\"${x*50-z*25},${y*50}!\", label=\"$label\", fillcolor=\"$color\", shape=$shape, orientation=$orientation];")
    // line(s"  $name [pos=\"${y*50},${z*50}!\", label=\"$label\", fillcolor=$color];")    // rotated for now
    // line(s"  $name [pos=\"${-z*50},${y*50}!\", label=\"$label\", fillcolor=$color];")    // rotated for now
    return Point(name, x, y, z)

  def edge(x: Point, y: Point) = 
    line(s"  ${x.s} -> ${y.s};")
    x

  def depth(path: String) = path.count(_!='0')-path.count(_=='0')

  def paths(n: Node[String]): (Map[String, Int], Map[String, Int]) = 
    var xs = mutable.Set[String]()
    var ys = mutable.Set[String]()

    def up(n: Node[String], path: String = "", total: String = ""): Unit = n match
      case OrdTree(l, _) => 
        ys += ""
        xs += "1"
        up(l, "1")
      case OTNone() => 
        if path.charAt(path.length-1) == '0' then ys += path+"0"*depth(path)
      case Trie(l, r) => 
        up(l, path + '1', total)
        up(r, path + '0', total)
      case Zipper(l, r) => 
        ys += path
        val nath = path.map(_ match {case '0'=>'1'; case '1'=>'0'})
        var tot = total
        for n <- l do
          tot += path
          xs += tot+'1'
          down(n, path, tot)
        tot = total
        for n <- r do 
          tot += nath
          xs += tot+'1'
          down(n, path, tot)

    def down(rstack: List[Node[String]], path: String, total: String = ""): Unit = rstack match
      case Nil => {}
      case n :: ns =>
        val truncate = path.slice(0, path.lastIndexOf('1'))
        up(n, truncate+'0', total)
        down(ns, truncate, total)

    up(n)
    return (xs.toList.sorted.zipWithIndex.toMap, ys.toList.sorted.zipWithIndex.toMap)
  
  val (xs, ys) = paths(n)
  println(xs)
  println(ys)

  def gety(path: String) = 
    val d = depth(path)
    ys.get(path+"0"*d).get*2 - d

  def getx(total: String) = 
    val d = depth(total)
    xs.get(total+"0"*d+"1").get*2
    
  def up(n: Node[String], path: String = "", total: String = ""): Option[Point] =
    val hash = n.hashCode()
    // println(s"$hash\t<- $n")
    val ret = n match
      case OrdTree(l, v) => 
        val p = point(getx(total), label=v.getOrElse(""), color=ORANGE, shape=if total == "" then "house" else "cylinder")
        up(l, "1") match
          case Some(pl) => Some(edge(p, pl))
          case None => Some(p)
      case OTNone() => None
      case Trie(l, r) => 
        up(r, path+'0', total) match
          case Some(pr) => 
            val p = edge(point(pr.x, gety(path), pr.z+1, color=GREEN), pr)
            up(l, path+'1', total) match
              case Some(pl) => Some(edge(p, pl))
              case None => Some(p)
          case None =>
            up(l, path+'1', total) match
              case Some(pl) => Some(edge(point(pl.x, gety(path), pl.z-1, color=GREEN), pl))
              case None => None
      case Zipper(l, r) => 
        val p = point(getx(total), gety(path), 0, color=DARK_PINK, shape="square", orientation=45)
        // over(l, p, 1) ++ over(r, p, -1)
        val nath = path.map(_ match {case '0'=>'1'; case '1'=>'0'})
        var tot = total
        var p2 = p
        for n <- l do
          tot += path
          down(n, path, tot) match
            case Some(pl) => edge(p2, pl); p2 = pl
            case None => {}
        tot = total
        p2 = p
        for n <- r do 
          tot += nath
          down(n, path, tot) match
            case Some(pr) => edge(p2, pr); p2 = pr
            case None => {}

        Some(p)
    // println(s"$hash\t-> $ret")
    ret


  def down(stack: List[Node[String]], path: String, total: String): Option[Point] =
    def down(stack: List[Node[String]], path: String, total: String): Option[Point] = stack match
      case n :: ns => n match
        case OrdTree(_, _) => up(n, "0", total)
        case _ =>
          val truncate = path.slice(0, path.lastIndexOf('1'))
          println((path, truncate+'0', total, n))
          val p2 = point(getx(total), gety(truncate), depth(truncate), color=BLUE, shape="Mcircle")
          down(ns, truncate, total) match
            case Some(p) => Some(edge(p2, p))
            case None => None
          up(n, truncate+'0', total) match
            case Some(p) => Some(edge(p2, p))
            case None => None
          Some(p2)
      case _ => None
    down(stack, path, total) match 
      case Some(p) => Some(edge(point(getx(total), gety(path), depth(path), color=LIGHT_PINK, shape="square", orientation=45), p))
      case None => None
      
      // edge(p, p2) :: down(ns, p2)

  up(n)
  line("}")
  pw.close
  



/*
TODO:
  - draw
  - test
  - use in interpreter as env
  - write it up
*/