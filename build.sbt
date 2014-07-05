name := "tracing"

version := "0.1"

scalaOrganization := "org.scala-lang.virtualized"

scalaVersion := "2.10.2"

libraryDependencies += "org.scala-lang.virtualized" % "scala-compiler" % "2.10.2"

libraryDependencies += "org.scala-lang.virtualized" % "scala-library" % "2.10.2"

libraryDependencies += "org.scalatest" % "scalatest_2.10" % "2.2.0" % "test"

scalacOptions += "-Yvirtualize"

scalacOptions += "-deprecation"

offline := true