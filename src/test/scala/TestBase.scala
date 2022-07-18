import org.junit.Test
import org.junit.Assert.*

class TestBase:
  def assertStr[S, T](s: S, t: T): Unit =
    assertEquals(t.toString, s.toString)

  def assertStrs[S, T](ss: List[S], t: T): Unit =
    for (s <- ss) assertStr(s, t)
