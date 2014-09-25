package usage

import scala.util._

class Usage(val lib: Lib, val pantheon: Array[Lib]) {
}

object Usage {
  private def libread(s: String, olib: Option[Lib]) = {
    val f = (new java.io.File(s)).getCanonicalFile
    olib.filter(_.file == f).map(x => Right(x)).getOrElse{ 
      Lib.read(f, olib)
    }
  }
  
  def source(s: String) = libread(s, None)
  def source(s: String, l: Lib) = libread(s, Some(l))
  
  def apply(l: Lib, sources: Seq[String], docs: Option[java.io.File] = None): Either[Vector[String], Usage] = {
    val pantheonBuilder = Array.newBuilder[Lib]
    val errorBuilder = Vector.newBuilder[String]
    val outcomes = new Array[Either[String,String]](sources.length)
    for ((s,i) <- sources.zipWithIndex) {
      source(s, l) match {
        case Right(x) => pantheonBuilder += x; outcomes(i) = Right(s)
        case Left(e) => errorBuilder ++= e; outcomes(i) = Left(s)
      }
    }
    val wrongs = outcomes.collect{ case Left(s) => s }
    if (wrongs.length > 0) {
      errorBuilder += (outcomes.length - wrongs.length).toString + " reads succeeded."
      errorBuilder += wrongs.length.toString + " reads failed:"
      wrongs.foreach{ w => errorBuilder += "  " + w }
      Left(errorBuilder.result)
    }
    else {
      val u = new Usage(l, pantheonBuilder.result)
      Right(u)
    }
  }
  
  def explain(t: java.lang.Throwable) = 
    t.toString + ": " + Option(t.getMessage).getOrElse("") + "\n" + t.getStackTrace.map("  "+_).mkString("\n")
}
