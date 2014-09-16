package usage

import scala.collection.mutable.{ AnyRefMap => RMap }

object MethodOverrides {
  def record(root: String, lib: Lib, other: Lib, known: RMap[String, RMap[String, List[String]]]): RMap[String, RMap[String, List[String]]] = {
    val r = lib.lookup.get(root) match {
      case None => return RMap.empty
      case Some(x) => x
    }
    if (other.extended.descendants contains r) {
      val annotated = RMap(r.name -> ())
      lib.descendants.get(r).outerNodeTraverser.foreach{ x => annotated += x.name -> () }
      other.extended.descendants.get(r).outerNodeTraverser.foreach{ x =>
        if (!(lib.lookup contains x.name)) {
          other.extended.ancestors.get(x).outerNodeTraverser.foreach{ a =>
            if (annotated contains a.name) {
              known getOrNull a.name match {
                case null => known += (a.name -> RMap("<>" -> List(x.name)))
                case m => m getOrNull "<>" match {
                  case null => m += ("<>" -> List(x.name))
                  case xs => m += ("<>" -> (x.name :: xs))
                }
              }
              val ms = known(a.name)
              (x.methods.filter(_.wraps.isEmpty).map(_.name).toSet & a.methods.map(_.name).toSet).foreach{ case name =>
                ms getOrNull name match {
                  case null => ms += name -> List(x.name)
                  case xs => ms += name -> (x.name :: xs)
                }
              }
            }
          }
        }
      }
    }
    known
  }
  def main(args: Array[String]) {
    if (args.length < 1) { println("First argument should be the root of the inheritance hierarchy"); sys.exit(1) }
    if (args.length < 2) { println("Second argument should be the .jar that contains the root file"); sys.exit(1) }
    val lib = Usage.source(args(1), true) match {
      case Right(x) => x
      case Left(e) => println("Error"); e.foreach(println); sys.exit(1)
    }
    if (!(lib.lookup contains args(0))) { println(s"Could not find ${args(0)} in ${args(1)}."); sys.exit(1) }

    var overrides = RMap.empty[String, RMap[String, List[String]]]
    val errorBuilder = Vector.newBuilder[Vector[String]]
    args.drop(2).foreach(s => Usage.source(s, lib, true) match {
      case Right(x) => overrides = record(args(0), lib, x, overrides)
      case Left(e) => errorBuilder += (("Error in "+ s) +: e)
    })
    val errors = errorBuilder.result
    if (errors.length > 0) {
      println(s"WARNING: ${errors.length} FILES FAILED TO READ")
      errors.flatMap(_.take(2) :+ "").foreach(x => println("  " + x))
    }
    else println(s"All ${args.length-2} target libraries loaded okay.")
    println(s"Found ${overrides.size} classes with external descendants")
    overrides.toList.sortBy(_._1).map(x => x._1 -> x._2.toList.sortBy(_._1).map(y => y._1 -> y._2.sorted)).foreach{ case (n, xs) =>
      println(n)
      xs.foreach{ case (m, ys) =>
        println("  " + m)
        ys.foreach(y => println("    " + y))
      }
    }
  }
}
