
package types

import ordmap.*
import ordinals.*
import util.*

import eval.evalZ
import trace.Tracer
import Ordering._

import scala.collection.immutable.ListMap
import scala.collection.mutable.Map
import spire.math.Natural

/// Types ///

type Sym = String

case class Op2(name: Sym, op: (Ordinal, Ordinal) => Ordinal):
  def apply(x: Ordinal, y: Ordinal): Ordinal = op(x, y)
val Plus  = Op2("+", _+_)
val Minus = Op2("-", _-_)
val Times = Op2("*", _*_)

sealed trait Term:
  def +(that: Term) = op("+")(this, that)
  def *(that: Term) = op("*")(this, that)
  def -(that: Term) = op("-")(this, that)
  def unary_-       = op("-")(   0, this)
  def ||(that: Term) = or(this, that)
  def apply(thats: Term*) = app(this, thats:_*)
  def norm = _norm(this)
  override def toString: String = _str(this)
  def debug: String = _debug(this)
sealed trait Val extends Term   // some terms are values (Val <: Term)
case class app(f: Term, t: Term) extends Term
object app: 
  def apply(f: Term, ts: Term*): Term = 
    if ts.length == 0 then f else app(app(f, ts.dropRight(1):_*), ts.last)
case class app0(f: Term, t: Term) extends Term
case class c(i: Ordinal) extends Val
case class clo(s: Sym, t: Term, nv: Env) extends Val
case class pclo(p: Term, t: Term, nv: Env) extends Val
case class err() extends Val
case class f() extends Term
object f:
  def apply(sy: Sym): s = s(sy, f())
  def apply(o: Ordinal): Term = if o==O0 then f() else spl(o.asOrd, f())
case class ifte(a: Term, b: Term, c: Term) extends Term
case class lam(s: Sym, t: Term) extends Term
object lam:
  def apply(t: Term): lam = lam("", t)
  def apply(i: Int, t: Term): lam = if i <= 1 then lam(t) else lam(lam(i-1, t))
  def apply(ss: List[Sym], t: Term): lam = lam(ss(0), if ss.length <= 1 then t else lam(ss.drop(1), t))
case class or(a: Term, b: Term) extends Term
case class plam(p: Term, t: Term) extends Term
object plam:
  def apply(t: Term): plam = plam(v(), t)
  def apply(i: Int, t: Term): plam = if i <= 1 then plam(t) else plam(plam(i-1, t))
  def apply(ss: List[Term], t: Term): plam = plam(ss(0), if ss.length <= 1 then t else plam(ss.drop(1), t))
case class lift(o: ord, t: Term) extends Term
object lift:
  def apply(t: Term): lift = lift(ω, t)
case class link(s: Sym) extends Term
case class op(op:Op2, a: Term, b: Term) extends Term
object op:
  def plus (a: Term, b: Term) = op(Plus , a, b)
  def minus(a: Term, b: Term) = op(Minus, a, b)
  def times(a: Term, b: Term) = op(Times, a, b)
  def apply(s: String): ((Term, Term) => Term) = s match
    case "+" => plus
    case "-" => minus
    case "*" => times
case class qq(o: ord, t: Term) extends Term
object qq:
  def apply(t: Term) = mk_qq_co(ω, t)
  def apply(o: Ordinal, t: Term) = if o==O0 then t else mk_qq_co(o.asOrd, t)
case class quo(o: ord, t: Term) extends Val
object quo:
  def apply(t: Term) = mk_quo(ω, t)
  def apply(o: Ordinal, t: Term) = if o==O0 then t else mk_quo(o.asOrd, t)
case class run(o: ord, t: Term) extends Term
object run:
  def apply(t: Term) = mk_run(ω, t)
  def apply(o: Ordinal, t: Term) = if o==O0 then t else mk_run(o.asOrd, t)
case class s(s: Sym, t: Term) extends Term
case class spl(o: ord, t: Term) extends Term
object spl:
  def apply(t: Term) = mk_spl_co(ω, t)
  def apply(o: Ordinal, t: Term) = if o==O0 then t else mk_spl_co(o.asOrd, t)
case class v() extends Term
object v:
  def apply(sy: Sym): s = s(sy, v())
  def apply(o: Ordinal): Term = if o==O0 then v() else spl(o.asOrd, v())

////

def isVal(t: Term)(using Env): Boolean = t match
  case quo(o, s) => !(Env.size >> o) // may contain dominating splices
  case t: Val    => true
  case _         => false

implicit def C(i: Int): c = c(i)

def debug(t: Term): Unit = println(t.debug)
  
// some macros
def spl1(t: Term) = spl(O1, t)
def qq1(t: Term)  = qq(O1, t)
def qqq(t: Term)  = mk_qq_co(`ω²`, t)
def sss(t: Term)  = mk_spl_co(`ω²`, t)

// macros for use with app0 (dissolved apps), corresponding to alternative call conventions
// *A > *B because it doesn't require each ind to be incremented by 1
def appA(f: Term, ts: Term*): Term = 
  if ts.length == 0 then f else
    app0(spl1(appA(f, ts.dropRight(1):_*)), ts.last)
def appB(f: Term, ts: Term*): Term = 
  if ts.length == 0 then f else
    spl1(app0(appB(f, ts.dropRight(1):_*), ts.last))
def lamA(t: Term) = qq1(lam(t))
def lamB(t: Term) = lam(qq1(t))

// normalization (assume all o are non-zero)
// these are meant to be used (only) at run-time
def mk_quo(o: ord, t: Term): quo = t match
  case quo(p, s) if o <> p  => quo(o+p, s)
  case _                    => quo(o, t)
def mk_quo2(o: ord, t: Term): Term = t match
  case quo(p, s) if o <> p  => quo(o+p, s)
  case spl(p, s) if o <> p  =>  o ? p match 
    case EQ => s
    case _ => throw Unimplemented
  case _                    => quo(o, t)
def mk_run(o: ord, t: Term): run = t match
  case run(p, s) if o <> p  => run(o+p, s)
  case _                    => run(o, t)
def mk_qq(o: ord, t: Term): Term = t match
  case qq(p, s)  if o <> p  => qq(o+p, s)
  case spl(p, s) if o <> p  => o ? p match 
    case GT => qq((o-p).asOrd, s)
    case LT => spl((p-o).asOrd, s)
    case EQ => s
  case _                    => qq(o, t)
def mk_spl(o: ord, t: Term): Term = t match
  case spl(p, s) if o <> p  => spl(o+p, s)
  case qq(p, s)  if o <> p  => o ? p match 
    case GT => spl((o-p).asOrd, s)
    case LT => qq((p-o).asOrd, s)
    case EQ => s
  case quo(p, s) if o <> p  => o ? p match 
    case GT => spl((o-p).asOrd, s)
    case LT => quo((p-o).asOrd, s)
    case EQ => s
  case _                    => spl(o, t)

// like mk_* but with only combination, no cancellation
def mk_qq_co(o: ord, t: Term): qq = t match
  case qq(p, s)  if o <> p  => qq(o+p, s)
  case _                    => qq(o, t)
def mk_spl_co(o: ord, t: Term): spl = t match
  case spl(p, s) if o <> p  => spl(o+p, s)
  case _                    => spl(o, t)

// def mk_sh(so: SOrdinal, t: Term): Term = t match
//   case quo(o, t)  => if so == -o then t else mk_sh(so+o, t) // NOTE: mk_sh so that ,,'`x ~> x
//   case sh(so2, t) => if so == -so2 then t else sh(so+so2, t)
//   case _          => sh(so, t)

def _norm(t: Term): Term = t match
  case s(sym, t)      => s(sym, _norm(t))
  case quo(o, t)      => mk_quo(o, _norm(t))
  case lam(s, t)      => lam(s, _norm(t))
  case app(f, t)      => app(_norm(f), _norm(t))
  case ifte(x, y, z)  => ifte(_norm(x), _norm(y), _norm(z))
  case _              => t

sealed trait Type:
  override def toString: String = _str(this)
  def debug: String = _debug(this)
case class _c() extends Type
case class _lam(a: Type, b: Type) extends Type
case class _quo(ty: Type) extends Type

type Env = OM[(Sym, (Val, Val))]
def lookup(env: Env, s: Sym) = env.find(t => t._1 == s)._2
object Env:
  def empty: Env = nil()
  def current(using env: Env): Env = env
  def size(using env: Env) = env.size
  def debug(using env: Env) = env.debug
  def apply(s: Sym)(using env: Env): (Val, Val) = lookup(env, s)
  def apply(o: Ordinal)(using env: Env): (Val, Val) = env(o)._2
  def chop(s: Sym)(using env: Env): Env = env.seek(t => t._1 == s)
  def chop(o: Ordinal)(using env: Env): Env = env.chop(o)
  // def shift(so: SOrdinal)(using env: Env): Env = env.shift(so)
  def pad(o: Ordinal)(using env: Env): Env = env.pad(o)
  def head(using env: Env): (Val, Val) = env.head._2
  def level(using env: Env): Ordinal = env.level
  def isLevelZero(using env: Env): Boolean = env.isLevelZero


type DEnv = DOM[(Sym, (Val, Val))]
def lookup(denv: DEnv, s: Sym): (Val, Val) = lookup(denv.om, s)
object DEnv:
  def empty: DEnv = DOM(Env.empty, nil())
  def current(using denv: DEnv): DEnv = denv
  def size(using denv: DEnv) = denv.size
  def debug(using denv: DEnv) = denv.debug
  def apply(s: Sym)(using denv: DEnv): (Val, Val) = lookup(denv.om, s)
  def apply(o: Ordinal)(using denv: DEnv): (Val, Val) = denv(o)._2
  // def chop(s: Sym)(using denv: DEnv): DEnv = denv.seek(t => t._1 == s)
  def chop(o: Ordinal)(using denv: DEnv): DEnv = denv.chop(o)
  // def shift(so: SOrdinal)(using denv: DEnv): DEnv = denv.shift(so)
  def pad(o: Ordinal)(using denv: DEnv): DEnv = denv.pad(o)
  def head(using denv: DEnv): (Val, Val) = denv.head._2
  def level(using denv: DEnv): Ordinal = denv.level
  def isLevelZero(using denv: DEnv): Boolean = denv.isLevelZero

class Code(tc: Term):
  val t: Term = tc match
    case quo(o, t) => t // TODO: what if o != ω
    case _         => err()
  def apply()(using Tracer): Val = evalZ(t)(using Env.empty, Lib.empty)

// type Lib = Map[Sym, Code]
// object Lib:
//   def empty: Lib = Map.empty
//   def current(using lib: Lib): Lib = lib
//   def apply(s: Sym)(using lib: Lib): Term = lib(s).t

type Lib = Map[Sym, Term]
object Lib:
  def empty: Lib = Map.empty
  def current(using lib: Lib): Lib = lib
  def apply(s: Sym)(using lib: Lib): Term = lib(s)


/// Vals ///

val pls = lam(2, v(1)+v())
val mul = lam(2, v(1)*v())

/// Printing ///

def t2c(t: Term): String = t match
  case app(_, _)      => " " // |@
  case app0(_, _)     => "@" // |@
  case ifte(_, _, _)  => "?" // ?:
  case lam(_, _)      => "λ" // λ.
  case plam(_, _)     => "~" // λ.
  case lift(_, _)     => "^"
  case or(_, _)       => "|" // v
  case qq(_, _)       => "`"
  case quo(_, _)      => "\'"
  case run(_, _)      => "%"
  case spl(_, _)      => ","
  case link(_)        => "$"
  case op(op, _, _)   => op.name
  case _              => "!" // no need to print

def needs_parens(t: Term): Boolean = t.isInstanceOf[app] || t.isInstanceOf[op]
def maybe_paren(t: Term): String = if needs_parens(t) then s"(${_str(t)})" else _str(t)
def mp(t: Term): String = maybe_paren(t)
implicit def _str(t: Term): String = t match
  case app(f, t)     => s"${mp(f)} ${mp(t)}"
  case app0(f, t) => s"${mp(f)} @ ${mp(t)}"
  case c(i)          => i.toString
  case clo(s, t, nv) => s"ƛ$s.${_str(t)}" // + s"@$nv"
  case pclo(p, t, nv)=> s"ƛ$p~${_str(t)}" // + s"@$nv"
  case err()         => "err"
  case ifte(a, b, c) => s"(${_str(a)} ? ${_str(b)} : ${_str(c)})"
  case lam(s, t)     => s"λ$s.${_str(t)}"
  case plam(p, t)    => s"λ$p~${_str(t)}"
  case link(s)       => s"$$$s"
  case or(a, b)      => s"(${_str(a)} || ${_str(b)})"
  case op(o, a, b)   => s"${_str(a)}${o.name}${_str(b)}" // [${o.name}]
  case spl(o, v()) if o < w => s"v${o}"    // [,n]v ~> vn
  case spl(o, f()) if o < w => s"f${o}"    // [,n]v ~> vn
  case spl (ord(a,n,b), s) if a==O1&&b==O0 => s"${t2c(t)*I(n)}${mp(s)}"
  case lift(ord(a,n,b), s) if a==O1&&b==O0 => s"${t2c(t)*I(n)}${mp(s)}"
  case qq  (ord(a,n,b), s) if a==O1&&b==O0 => s"${t2c(t)*I(n)}${mp(s)}"
  case quo (ord(a,n,b), s) if a==O1&&b==O0 => s"${t2c(t)*I(n)}${mp(s)}"
  case run (ord(a,n,b), s) if a==O1&&b==O0 => s"${t2c(t)*I(n)}${mp(s)}"
  case spl(o, s) => s"[${t2c(t)}$o]${mp(s)}"
  case lift(o, s) => s"[${t2c(t)}$o]${mp(s)}"
  case qq (o, s) => s"[${t2c(t)}$o]${mp(s)}"
  case quo(o, s) => s"[$o]${mp(s)}"
  case run(o, s) => s"[${t2c(t)}$o]${mp(s)}"
  case s(s, t) => s"s_$s(${_str(t)})"
  case v()     => "v"
  case f()     => "f"
  // case _       => "?"

def _debug(t: Term): String = t match
  case app(f, t)     => s"app(${_debug(f)}, ${_debug(t)})"
  case app0(f, t)    => s"app0(${_debug(f)}, ${_debug(t)})"
  case c(i)          => s"c($i)"
  case clo(s, t, nv) => s"clo($s, ${_debug(t)}, nv)"
  case pclo(p, t, nv)=> s"pclo(${_debug(p)}, ${_debug(t)}, nv)"
  case err()         => s"err()"
  case ifte(a, b, c) => s"ifte(${_debug(a)}, ${_debug(b)}, ${_debug(c)})"
  case lam(s, t)     => s"lam($s, ${_debug(t)})"
  case plam(s, t)    => s"plam($s, ${_debug(t)})"
  case link(s)       => s"link($s)"
  case or(a, b)      => s"or(${_debug(a)}, ${_debug(b)})"
  case op(o, a, b)   => s"op(${o.name}, ${_debug(a)}, ${_debug(b)})"
  case spl(o, s)     => s"spl($o, ${_debug(s)})"
  case lift(o, s)    => s"lift($o, ${_debug(s)})"
  case qq (o, s)     => s"qq($o, ${_debug(s)})"
  case quo(o, s)     => s"quo($o, ${_debug(s)})"
  case run(o, s)     => s"run($o, ${_debug(s)})"
  case s(s, t)       => s"s($s, ${_debug(t)})"
  case v()           => s"v()"
  case f()           => s"f()"
  // case _             => "?"

def needs_parens(ty: Type): Boolean = ty.isInstanceOf[_lam]
def maybe_paren(ty: Type): String = if needs_parens(ty) then s"(${_str(ty)})" else _str(ty)
implicit def _str(ty: Type): String = ty match
  case _c()       => "C"
  case _lam(a, b) => s"${_str(a)}->${_str(b)}"
  case _quo(ty)   => s"'${maybe_paren(ty)}"

def _debug(ty: Type): String = ty match
  case _c()       => s"_c()"
  case _lam(a, b) => s"_lam($a, $b)"
  case _quo(ty)   => s"_quo($ty)"

def log[T <: Term](t: T): T = 
  println(_str(t)); t
def log(t: Type): Type = 
  println(_str(t)); t

///


// FIXME: this will fail on (λx.`(λy.,`(,x + y))) ~> (λ.`(λ.,`(,v + v)))
//        we must use a double ended OM env, like in match so ,` doesn't lose information

// type NullEnv = OM[Sym]
// def v2i(term: Term): Term =
//   def v2i(term: Term)(using env: NullEnv): Term = term match
//     case app(f, t)      => app(v2i(f), v2i(t))
//     case ifte(a, b, c)  => ifte(v2i(a), v2i(b), v2i(c))
//     case lam(s, t)      => lam(v2i(t)(using env.cons1(s)))
//     case quo(o, t)      => quo(o, v2i(t)(using env.pad(o)))
//     case qq(o, t)       => qq(o, v2i(t)(using env.pad(o)))
//     case spl(o, t)      => spl(o, v2i(t)(using env.chop(o)))
//     case s(s, t)        => {
//       val o: Ordinal = env.indexOf(t => t == s)  // TODO: implement indexOf
//       spl(o, v2i(t)(using env.chop(o)))
//     }
//     case _              => term
//   v2i(term)(using nil())
