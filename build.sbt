val dottyVersion = "3.0.0-M2"

lazy val root = project
  .in(file("."))
  .settings(
    name := "Monocly",
    version := "0.1.0",
    scalacOptions += "-language:implicitConversions",
    scalaVersion := dottyVersion,
  )
