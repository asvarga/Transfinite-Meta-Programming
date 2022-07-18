
package util

def ----() = println(";" + "-"*30 + ";")

class AbsurdException extends Exception
val Absurd = AbsurdException()

class UnimplementedException extends Exception
val Unimplemented = UnimplementedException()

class IllegalPatternException extends Exception
val IllegalPattern = IllegalPatternException()