package usage

import scala.util._

object Usage {
  private def libread(s: String, olib: Option[Lib]) = {
    val f = (new java.io.File(s)).getCanonicalFile
    olib.filter(_.file == f).map(x => Right(x)).getOrElse{ 
      Lib.read(f, olib)
    }
  }
  
  def source(s: String) = libread(s, None)
  def source(s: String, l: Lib) = libread(s, Some(l))
  
  def explain(t: java.lang.Throwable) = 
    t.toString + ": " + Option(t.getMessage).getOrElse("") + "\n" + t.getStackTrace.map("  "+_).mkString("\n")
}
