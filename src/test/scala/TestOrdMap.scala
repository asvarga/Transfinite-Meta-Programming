import org.junit.Test
import org.junit.Assert.*

import ordinals.*
import ordmap.*

class TestOrdMap extends TestBase:
  
  val foo = nil()
    .cons("end")
    .padp(3)
    .cons("world")
    .padp(5)
    .cons("hello")
  val L = nil().cons1("foo").cons1("foo").pad(w).cons1("bar").cons1("quux")
  val M = nil().cons1("a").cons1("b").pad(w*w)

  @Test def t1(): Unit = 
    assertStr(foo, "hello()_()_()_()_()world()_()_()end()")
    assertStr(foo.head, "hello")
    assertStr(foo(0), "hello")
    assertStr(foo.chop(2), "_()_()_()world()_()_()end()")
    assertStr(foo(5), "world")
    assertStr(foo.chop(6), "_()_()end()")
    assertStr(foo(8), "end")
    assertStr(foo.chop(6).pad(ω), "_(())_()_()end()")
    assertStr(foo.cons("hi"), "hi()_()_()_()_()world()_()_()end()")
    assertStr(foo.cons1("hi"), "hi()hello()_()_()_()_()world()_()_()end()")
    // assertStr(foo.find(s => s(0) == 'w'), "world")
    assertStr((foo.size, foo.level), "(9,0)")
    assertStr(foo.pad(ω*3).level, "3")

  @Test def t2(): Unit = 
    assertStr(L, "quux()bar()_(())foo()foo()")
    assertStr(L(), "quux")
    assertStr(L(1), "bar")
    assertStr(L(w), "foo")
    assertStr(L.isLevelZero, "false")
    assertStr(L.chop(w).isLevelZero, "true")
    assertStr(L.size, "ω+2")
    assertStr(L.pad(ω*3).size, "ω*4+2")
    assertStr(L.pad(ω*3).level, "4")

  @Test def t3(): Unit = 
    assertStr(M, "_(()())b()a()")
    assertStr(M.chop(w), M)

