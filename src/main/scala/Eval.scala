
package eval

import trace.*
import types.*
import ordinals.*
import Ordering._
import util.*

import scala.collection.mutable

/// Eval ///

// entry point
def eval(t: Term)(using DEnv, Lib, Tracer): Term =
  if DEnv.isLevelZero then evalZ(t) else evalS(t)

// specialized to lvl==0
def evalZ(t: Term)(using DEnv, Lib, Tracer): Val =
  Tracer.post(t, Tracer.pre(t) match
    case t: Val           => t
    case v()              => DEnv.head._1
    case f()              => DEnv.head._2
    case s(s, t)          => err() // evalZ(t)(using DEnv.chop(s))
    case qq(o, t) => 
      mk_quo(o, eval(t)(using DEnv.pad(o)))  // goto eval
    case lift(o, t) => 
      mk_quo(o, evalZ(t))
    case run(o, t) => evalZ(mk_spl(o, evalZ(t)(using DEnv.empty)))(using DEnv.empty)
    case spl(o, t) => evalZ(t)(using DEnv.chop(o))
      // o ? DEnv.size match
      // case LT => evalZ(t)(using DEnv.chop(o))
      // case EQ => evalZ(t)(using DEnv.empty)
      // case GT => 
      //   val u = evalZ(t)(using DEnv.empty)     // empty the DEnv
      //   u match
      //     case u: quo => evalZ(mk_spl((o-DEnv.size).asOrd, u))  // continue upwards
      //     case _ => err()
    case lam(s, t)        => clo(s, t, DEnv.current)
    case plam(s, t)       => pclo(s, t, DEnv.current)
    case link(s)          => evalZ(Lib(s))
    case app(f, t)        => (evalZ(f), evalZ(t)) match
      case (f@clo(s, b, nv), t) => evalZ(b)(using nv.cons1((s, (t, f))))
      case (f@pclo(p, b, nv), t) => mtch(p, t) match
        case None => 0
        case Some(m) => 
          // println(m)
          def v2o(t: Term): Ordinal = t match
            case v() => O0
            case spl(o, v()) => o
            case _ => throw Absurd
          val kvs = m.toList.filter(!_._1.isInstanceOf[link]).sortBy(t=>v2o(t._1))(using OrdinalOrdering)
          // println(kvs.toMap)
          def build(kvs: List[(Term, Term)]): DEnv = kvs match
            case (k1,v1)::(k2,v2)::kvs => build((k2,v2)::kvs).pad(v2o(k2)-v2o(k1)).cons(("", (v1.asInstanceOf[Val], err())))
            case (k,v)::kvs => nv.cons1((k, (v.asInstanceOf[Val], f))) // TODO: attach f here or other end or everywhere?
            case Nil => nv
          val bkvs = build(kvs)
          // println(bkvs)
          evalZ(b)(using bkvs)
      case _ => err()
    // dissolved app:
    case app0(f, t) => (evalZ(f), evalZ(t)) match
      case (f@clo(s, b, nv), t) => evalZ(b)(using nv.cons((s, (t, f))))
      case _ => err()
    case ifte(x, y, z) => evalZ(x) match
      case c(i) => if (i>0) then evalZ(y) else evalZ(z)
      case _ => err()
    case or(a, b) => 
      val u = evalZ(a) 
      if u == c(0) then evalZ(b) else u
    case op(o, a, b) => (evalZ(a), evalZ(b)) match
      case (c(a), c(b)) => c(o.op(a, b))
      case _ => err()
    // case _ => err()
  )

// specialized to lvl!=0
def evalS(t: Term)(using DEnv, Lib, Tracer): Term =
  Tracer.post(t, Tracer.pre(t) match
    case quo(o, s)        => // must be before `case t: Val`
      if DEnv.size >> o then  // we may have contained dominating splices
        mk_quo(o, evalS(s)(using DEnv.pad(o)))
      else
        t
    case t: Val           => t
    case lift(o, s)       => lift(o, evalS(s))
    case v()              => t
    case f()              => t
    case s(s, t)          => err() // evalS(t)(using DEnv.chop(s))
    // case sh(so, t)        => mk_sh(so, eval(t)(using DEnv.shift(so)))
    // 6 cases for sh! TODO: simplify (split on: |DEnv|+so? |DEnv|>>o?)
    case qq(o, t) => 
      val u = evalS(t)(using DEnv.pad(o))
      if DEnv.size >> o then mk_qq_co(o, u) else mk_qq(o, u)
    case run(o, t) => run(o, evalS(t))
    case spl(o, t) =>
      if DEnv.size >> o then 
        val u = evalS(t)(using DEnv.chop(o)) // we know |DEnv| - o > w
        mk_spl_co(o, u)
      else mk_spl(o, eval(t)(using DEnv.chop(o)))
    case lam(s, t)        => lam(s, evalS(t)(using DEnv.pad(1)))
    case plam(p, t)       => plam(p, evalS(t))
    case link(s)          => evalS(Lib(s))
    case app(f, t)        => app(evalS(f), evalS(t))
    case app0(f, t)       => app0(evalS(f), evalS(t))
    case ifte(x, y, z)    => ifte(evalS(x), evalS(y), evalS(z))
    case or(x, y)         => or(evalS(x), evalS(y))
    case op(o, a, b)      => op(o, evalS(a), evalS(b))
    // case _ => err()
  )

/// Pattern Matching ///

/* 
TODO:
This is all terribly hacky.
We should really use a double ended ordinal map to store both the match map (e) and the depth (d).
The code layout should mimic that of eval/evalZ/evalS.
There is plenty of room to expand the set of legal patterns.
*/

type MEnv = mutable.Map[Term, Term]

def mtch(p: Term, t: Term): Option[MEnv] = 
  var e = mutable.Map[Term, Term]()
  def mtch(p: Term, t: Term)(using d: SOrdinal): Boolean = 
    // println(s"$p -><- $t // ${d}, ${e}")
    d match
      // zero
      case pos(z()) | neg(z()) => p match
        case v() => if (e.contains(v())) then (e(v())==t) else {e(v())=t; true}
        case link(s) => s=="_" || (if (e.contains(p)) then (e(p)==t) else {e(p)=t; true})
        case spl(o, p) => mtch(p, mk_quo(o, t))(using -o)
        case qq(o, p) => mtch(p, mk_spl(o, t))(using +o)
        case _ => throw IllegalPattern
      // negative
      case neg(d) if d < w => p match 
        case v() => 
          val dt = mk_spl(d.asOrd, t)
          if (e.contains(v(d))) then (e(v(d))==dt) else {e(v(d))=dt; true}
        case spl(o, p) => mtch(p, mk_quo(o, t))(using -o)
        case qq(o, p) => mtch(p, mk_spl(o, t))(using +o)
        case _ => throw IllegalPattern
      // positive
      case pos(d) if d >= w => (p, t) match
        case (p:quo, t)     if !(d >> p.o) => mtch(p.t, mk_spl(p.o, t))(using p.o+d)
        case (p:quo, t:quo) if t.o >= p.o  => mtch(p.t, mk_spl(p.o, t))(using p.o+d) // could do p==t in some cases
        case (p:qq, t)      if !(d >> p.o) => mtch(p.t, mk_spl(p.o, t))(using p.o+d)
        case (p:qq, t:qq)   if t.o >= p.o  => mtch(p.t, mk_spl(p.o, t))(using p.o+d)
        case (p:spl, t)     if !(d >> p.o) => mtch(p.t, mk_quo2(p.o, t))(using -p.o+d)
        case (p:spl, t:spl) if t.o >= p.o  => mtch(p.t, mk_quo2(p.o, t))(using -p.o+d)
        
        case (p:op, t:op) => (p.op==t.op) && mtch(p.a, t.a) && mtch(p.b, t.b)
        case (p:lam, t:lam) => mtch(p.t, t.t)
        case (p:plam, t:plam) => mtch(p.p, t.p) && mtch(p.t, t.t)
        case (p:app, t:app) => mtch(p.f, t.f) && mtch(p.t, t.t)
        case (p:app0, t:app0) => mtch(p.f, t.f) && mtch(p.t, t.t)
        case (p:ifte, t:ifte) => mtch(p.a, t.a) && mtch(p.b, t.b) && mtch(p.c, t.c)
        case _ => p==t
      case _ => throw IllegalPattern
  if mtch(p, t)(using 0) then Some(e) else None