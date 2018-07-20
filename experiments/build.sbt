name := "experiments"

scalaVersion := "2.11.8"

lazy val welder = ProjectRef(file("/home/raya/Desktop/Summer2018/welder"), "root")

lazy val root = (project in file(".")).dependsOn(welder)
