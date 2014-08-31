package scasm

import scala.util._
import scala.collection.mutable.{ AnyRefMap => RMap }
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
  def isStatic = (access & ACC_STATIC) != 0
  def protection = (access & (ACC_PUBLIC | ACC_PROTECTED | ACC_PRIVATE)) match {
    case ACC_PUBLIC => -1
    case ACC_PROTECTED => 0
    case ACC_PRIVATE => 1
    case x => throw new Exception("What kind of access is " + x.toHexString + "?")
  }
  def str(from: Klas) = if (from eq in.value) s"Meth($name, ${params.mkString(", ")}, ^)" else toString
  override def toString = s"Meth($name, ${params.mkString(", ")}, $in)"
}
object NoMeth extends Meth("", -1, Array.empty[String], V(NoKlas)) { override def toString = "Meth()" }

case class Klas(name: String, sig: String, access: Int, parents: Array[String], fields: Array[String], methods: Array[Meth], calls: Array[Call]) extends Named {
  def isSingle = fields contains "MODULE$"
  def isTrait = (access & ACC_INTERFACE) != 0
  def isImpl = name.endsWith("$class") && isAbstract && methods.forall(_.isStatic)
  def isAbstract = (access & ACC_ABSTRACT) != 0
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

class Inherit(val me: Klas, val companion: Option[Klas], val impl: Option[Klas]) extends Named {
  var touched: Inherit = NoInherit
  val ancestors = RMap[String, Inherit]()
  val descendants = RMap[String, Inherit]()
  def withCompanion(k: Klas) = new Inherit(me, Some(k), impl)
  def withImpl(k: Klas) = new Inherit(me, companion, Some(k))
  def isSingle = me.isSingle
  def isTrait = me.isTrait
  def isImpl = me.isImpl
  def name = me.name
  override def toString = "x" + companion.map(_ => "c").mkString + impl.map(_ => "i").mkString
}
object NoInherit extends Inherit(NoKlas, None, None) {}

class Lib(val klases: Array[Klas]) {
  lazy val inheritance = {
    val inh = RMap[String, Inherit]()
    for (k <- klases) { inh += (k.name, new Inherit(k, None, None)) }
    val names = inh.map{ case (n,_) => n }.toArray
    for (n <- names if inh contains n) {
      var k = inh(n)
      val nc = n + "$"
      val c = inh.getOrNull(nc)
      if (!k.isSingle && c != null && c.isSingle) {
        val kc = k withCompanion c.me
        inh += (n, kc)
        inh += (nc, kc)
        k = kc
      }
      if (k.isTrait) {
        val ni = n + "$class"
        val i = inh.getOrNull(ni)
        if (i != null && i.isImpl) {
          val ki = k withImpl i.me
          inh += (n, ki)
          inh += (ni, ki)
          if (k.companion.isDefined) inh += (nc, ki)
        }
      }
    }
    val ks = inh.map{ case (_,i) => i.me.name }.toSet.toArray.sorted.map(n => inh(n))
    for (k <- ks) {
      for (np <- k.me.parents) {
        val p = inh.getOrNull(np)
        if (p != null) {
          k.ancestors += (np, p)
          p.descendants += (k.name, k)
        }
      }
    }
    inh
  }
}
object Lib {
  def read(f: java.io.File, listen: Call => Boolean = _ => true): Either[Vector[String], Lib] = {
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
      if (problems.length > 0) Left(problems) else Right(new Lib(ks.result))
    } match {
      case Success(x) => x
      case Failure(t) => Left(Vector("Problem reading source library " + f.getCanonicalFile.getPath, Usage.explain(t)))
    }
  }
}


class Usage {
}

object Usage {
  def source(s: String) = Lib.read(new java.io.File(s), _ => false)
  
  def explain(t: java.lang.Throwable) = 
    t.toString + ": " + Option(t.getMessage).getOrElse("") + "\n" + t.getStackTrace.map("  "+_).mkString("\n")
}
