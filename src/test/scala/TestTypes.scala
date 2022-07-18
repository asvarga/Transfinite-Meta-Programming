import org.junit.Test
import org.junit.Assert.*

import types.*
import ordmap.*
import ordinals.*

class TestTypes extends TestBase:

  @Test def t1(): Unit = 
    given Env = nil[(Sym, (Val, Val))]()
      .cons(("end",   (c(555), c(666))))
      .padp(3)
      .cons(("world", (c(333), c(444))))
      .padp(5)
      .cons(("hello", (c(111), c(222))))
    assertStr(Env.current, "(hello,(111,222))()_()_()_()_()(world,(333,444))()_()_()(end,(555,666))()")
    assertStr(Env(5), "(333,444)")
    // assertStr(Env("end"), "(555,666)")
