import org.junit.Test
import org.junit.Assert.*

import parser.*

class TestParser extends TestBase:

  def assertRoundTrip(input: String): Unit =
    assertStr(P(input), input)

  @Test def t1(): Unit = 
    assertRoundTrip(",(,(,(λ.`λ.`λ.`(,v+,,v+,,,v) '''10) ''20) '30)")
