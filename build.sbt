val dottyVersion = "0.25.0"

lazy val root = project
  .in(file("."))
  .settings(
    name := "Monocly",
    version := "0.1.0",
    scalacOptions += "-language:implicitConversions",
    scalaVersion := dottyVersion,
    libraryDependencies += "org.scalameta" %% "munit" % "0.7.2" % "test",
    testFrameworks += new TestFramework("munit.Framework")
  )
