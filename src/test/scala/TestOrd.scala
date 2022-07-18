import org.junit.Test
import org.junit.Assert.*

import ordinals.*
import Ordering._

class TestOrd extends TestBase:

  val x = ord(2, 3, 4)

  @Test def string(): Unit = 
    assertStr(O0, "0")
    assertStr(O(5), "5")
    assertStr(x, "ω²*3+4")
    assertStr(ord(x, 5, x), "ω^(ω²*3+4)*5+ω²*3+4")
    assertStr(ord(x, 5, 0), "ω^(ω²*3+4)*5")
    assertStr(ord(x, 1, x), "ω^(ω²*3+4)+ω²*3+4")
    assertStr(ord(x, 1, 0), "ω^(ω²*3+4)")
    assertStr(ord(ω, 1, 0), "ω^ω")
    assertStr(ord(ord(ω, 1, 0), 1, 0), "ω^(ω^ω)")
    assertStr(ω, "ω")

  @Test def arithmetic(): Unit =
    assertEquals(List(x?x, x<x, x<=x, x==x), List(EQ, false, true, true))
    assertStr((x + x), "ω²*6+4")
    assertStr((x - x), "0")
    assertStr((x * x), "ω⁴*3+ω²*12+4")
    assertStr((x - ord(2, 3, 2)), "2")
    assertStr((ω + 2), "ω+2")

  @Test def signed(): Unit =
    assertStr(x: SOrdinal, "+ω²*3+4")
    assertStr(7: SOrdinal, "+7")
    assertStr(pos(x): SOrdinal, "+ω²*3+4")
    assertStr(neg(x): SOrdinal, "-ω²*3-4")
    assertStr(-x, "-ω²*3-4")
    assertStr(pos(x+w) + pos(x), "+ω²*6+4")
    assertStr(pos(x+w) + neg(x), "+ω")
    assertStr(pos(x+w) - pos(x), "+ω")
    assertStr(pos(x) * neg(x), "-ω⁴*3-ω²*12-4")
    assertStr(x * -x, "-ω⁴*3-ω²*12-4")
    assertStr(+x, "+ω²*3+4")
    assertStr(+w, "+ω")
