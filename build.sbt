val scala3Version = "3.1.0"

lazy val root = project
  .in(file("."))
  .settings(
    name := "TFDBI",
    version := "0.1.0-SNAPSHOT",

    scalaVersion := scala3Version,

    // `~ run` should rerun when example files change
    watchSources += baseDirectory.value / "examples",

    libraryDependencies += "com.novocode" % "junit-interface" % "0.11" % "test",
    libraryDependencies += "org.typelevel" %% "spire" % "0.18.0-M1",
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1"
  )
