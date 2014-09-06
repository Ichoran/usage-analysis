package scasm

import scala.util._
import scala.collection.mutable.{ AnyRefMap => RMap }
import scalax.collection.mutable.Graph
import scalax.collection.GraphPredef._
import scalax.collection.GraphEdge._
import org.objectweb.asm
import asm.Opcodes._

trait Named { def name: String }

case class V[A <: Named](var value: A) { override def toString = "{" + value.name + "}" }

case class Call(op: Int, name: String, params: Array[String], in: V[Meth]) extends Named {
  def str(from: Meth) = if (from eq in.value) s"Call($op, $name, ${params.mkString(", ")}, ^)" else toString
  override def toString = s"Call($op, $name, ${params.mkString(", ")}, $in)"
}
object NoCall extends Call(-1, "", Array.empty[String], V(NoMeth)) { override def toString = "Call()" }

case class Meth(name: String, access: Int, params: Array[String], in: V[Klas]) extends Named {
  lazy val id = name + ".." + params.mkString("..")
  def isStatic = (access & ACC_STATIC) != 0
  def protection = (access & (ACC_PUBLIC | ACC_PROTECTED | ACC_PRIVATE)) match {
    case ACC_PUBLIC => -1
    case ACC_PROTECTED => 0
    case ACC_PRIVATE => 1
    case x => throw new Exception("What kind of access is " + x.toHexString + "?")
  }
  def str(from: Klas) = if (from eq in.value) s"Meth($name,, ${params.mkString(", ")},, ^)" else toString
  override def toString = s"Meth($name,, ${params.mkString(", ")},, $in)"
}
object NoMeth extends Meth("", -1, Array.empty[String], V(NoKlas)) { override def toString = "Meth()" }

case class Klas(name: String, sig: String, access: Int, parents: Array[String], fields: Array[String], methods: Array[Meth], calls: Array[Call]) extends Named {
  def isSingle = fields contains "MODULE$"
  def isTrait = (access & ACC_INTERFACE) != 0
  def isImpl = name.endsWith("$class") && isAbstract && methods.forall(_.isStatic)
  def isAbstract = (access & ACC_ABSTRACT) != 0
  def isFinal = (access & ACC_FINAL) != 0
  override def toString = s"Klas($name, $sig, $access,, ${parents.mkString(", ")},, ${fields.mkString(", ")},, ${methods.map(_.str(this)).mkString(", ")},, ${calls.mkString(", ")})"
}
object NoKlas extends Klas("", "", -1, Array.empty[String], Array.empty[String], Array.empty[Meth], Array.empty[Call]) { override def toString = "Klas()" }

class KlasExtractor private (listen: Call => Boolean) extends asm.ClassVisitor(ASM5) {
  private[this] val myKlas: V[Klas] = V(NoKlas)
  private[this] var myMeths: List[V[Meth]] = Nil
  private[this] var myCalls: List[V[Call]] = Nil
  private[this] var myFields: List[String] = Nil
  def from(cr: asm.ClassReader): Either[String, Klas] = {
    Try{ cr.accept(this, 0) } match {
      case Failure(t) => Left(Usage.explain(t))
      case Success(_) => Right(myKlas.value)
    }
  }
  
  object MethExtractor extends asm.MethodVisitor(ASM5) {
    override def visitMethodInsn(op: Int, owner: String, name: String, desc: String, itf: Boolean) {
      val c = Call(op, name, Array(owner, desc), myMeths.head)
      if (listen(c)) myCalls = V(c) :: myCalls
    }
  }
  
  override def visit(ver: Int, acc: Int, name: String, sig: String, sup: String, iface: Array[String]) {
    myKlas.value = myKlas.value.copy(name = name, sig = sig, access = acc, parents = if (iface.isEmpty) Array(sup) else sup +: iface)
  }
  override def visitSource(src: String, dbg: String) {}
  override def visitOuterClass(owner: String, name: String, desc: String) {}
  override def visitAnnotation(desc: String, vis: Boolean) = null
  override def visitAttribute(attr: asm.Attribute) {}
  override def visitInnerClass(name: String, outName: String, inName: String, acc: Int) {}
  override def visitField(acc: Int, name: String, desc: String, sig: String, v: Object) = {
    myFields = name :: myFields
    null
  }
  override def visitMethod(acc: Int, name: String, desc: String, sig: String, exc: Array[String]) = {
    myMeths = V(Meth(name, acc, Array(sig, desc), myKlas)) :: myMeths
    MethExtractor
  }
  override def visitEnd {
    myKlas.value = myKlas.value.copy(
      fields = myFields.toArray.reverse,
      methods = myMeths.reverseMap(_.value).toArray,
      calls = myCalls.reverseMap(_.value).toArray
    )
  }
}
object KlasExtractor {
  def apply(cr: asm.ClassReader, listen: Call => Boolean = _ => true): Either[String, Klas] = (new KlasExtractor(listen)).from(cr)
  
  def apply(is: java.io.InputStream): Either[String, Klas] = apply(new asm.ClassReader(is))
  def apply(b: Array[Byte]): Either[String, Klas] = apply(new asm.ClassReader(b))
  def apply(s: String): Either[String, Klas] = apply(new asm.ClassReader(s))
}

class Lib(val klases: Array[Klas], val stdlib: Option[Lib]) { self =>
  lazy val (ancestors, descendants, relatives, specialized, lookup) = {
    val pBuild = Vector.newBuilder[(Klas, Klas)]   // Vector to avoid Array's invariance
    val names = klases.map(x => x.name -> x).toMap
    for (k <- klases; p <- k.parents; kp <- names.get(p)) pBuild += kp -> k
    val pairs = pBuild.result
    val anc = Graph(pairs.map{ case (kp, k) => k ~> kp }: _*)
    val dec = Graph(pairs.map{ case (kp, k) => kp ~> k }: _*)
    val rel = {
      val links = names.toList.flatMap{ case (_,k) =>
        if (k.isSingle) Nil
        else {
          val o = names.get(k.name + "$").filter(_.isSingle).toList
          val t = names.get(k.name + "$class").filter(_.isImpl).toList
          (o ++ t) match {
            case Nil => Nil
            case a :: Nil => a~k :: Nil
            case a :: b :: Nil => a~k :: b~k :: a~b :: Nil
            case _ => throw new Exception("Huh???")
          }
        }
      }
      Graph(links: _*)
    }
    val templ = {
      val spRegex = """(.+)\$mc(\w+)\$sp""".r
      val spMap = new RMap[String, List[Klas]]()
      klases.foreach(k => k.name match {
        case spRegex(base, spec) => spMap getOrNull base match {
            case null => names.get(base).foreach(c => spMap += (base, c :: k :: Nil))
            case c :: rest => spMap += (base, c :: k :: rest)
            case _ => throw new Exception("Invalid empty list in specialization map...how'd that happen???")
          }
        case _ =>  // Not a specialized class, ignore it.
      })
      Graph(spMap.map(_._2).toList.flatMap(x => x.headOption.toList.flatMap(x0 => x.drop(1).map(x0 ~ _))): _*)
    }
    (anc, dec, rel, templ, names)
  }
  object extended {
    val (ancestors, descendants) = stdlib match {
      case None => (self.ancestors, self.descendants)
      case Some(lib) =>
        val anc = (self.ancestors ++ lib.ancestors)
        val dec = (self.descendants ++ lib.descendants)
        for (k <- klases; p <- k.parents; xp <- lib.lookup.get(p)) {
          anc += k ~> xp
          dec += xp ~> k
        }
        (anc, dec)
    }
  }
  object methods {
    val ancestry: Map[String, Array[Meth]] = {
      lookup.map{ case (k,v) => k -> {
        v.methods.filter(! _.isStatic)
        // Need logic to find full tree (via method id, hopefully)
      }}
    }
  }
  def upstream(s: String) = lookup.get(s).flatMap(x => Try{ ancestors.get(x).outerNodeTraverser.toArray }.toOption )
  def downstream(s: String) = lookup.get(s).flatMap(x => Try { descendants.get(x).outerNodeTraverser.toArray }.toOption )
  def alike(s: String) = lookup.get(s).flatMap(x => Try { relatives.get(x).outerNodeTraverser.toArray }.toOption )
}
object Lib {
  def read(f: java.io.File, listen: Call => Boolean = _ => true, lib: Option[Lib]): Either[Vector[String], Lib] = {
    if (!f.exists) return Left(Vector("Source library does not exist: " + f.getCanonicalFile.getPath))
    Try {
      val zf = new java.util.zip.ZipFile(f)
      val ks = Array.newBuilder[Klas]
      val ts = Vector.newBuilder[String]
      try {
        val e = zf.entries
        while (e.hasMoreElements) {
          val ze = e.nextElement
          if (ze.getName.endsWith(".class")) {
            Try{ KlasExtractor(zf.getInputStream(ze)) match {
              case Left(t) => ts += t
              case Right(k) => ks += k
            }} match {
              case Success(_) =>
              case Failure(t) => ts += ("Exception reading entry " + ze.getName) + Usage.explain(t)
            }
          }
        }
      } finally zf.close
      val problems = ts.result
      if (problems.length > 0) Left(problems) else Right(new Lib(ks.result, lib))
    } match {
      case Success(x) => x
      case Failure(t) => Left(Vector("Problem reading source library " + f.getCanonicalFile.getPath, Usage.explain(t)))
    }
  }
}


class Usage {
}

object Usage {
  def source(s: String) = Lib.read(new java.io.File(s), _ => false, None)
  def source(s: String, l: Lib) = Lib.read(new java.io.File(s), _ => false, Some(l))
  
  def explain(t: java.lang.Throwable) = 
    t.toString + ": " + Option(t.getMessage).getOrElse("") + "\n" + t.getStackTrace.map("  "+_).mkString("\n")
}
