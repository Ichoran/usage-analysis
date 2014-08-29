package scasm

import scala.util._
import org.objectweb.asm
import asm.Opcodes._

case class V[A](var value: A) {}

case class Call(op: Int, owner: String, params: Array[String]) {}
object NoCall extends Call(-1, "", Array.empty[String]) { override def toString = "Call()" }

case class Meth(name: String, params: Array[String], wraps: Call = NoCall) {}
object NoMeth extends Meth("", Array.empty[String], NoCall) { override def toString = "Meth()" }

case class Klas(name: String, sig: String, access: Int, parents: Array[String], methods: Array[Meth], calls: Array[Call]) {}
object NoKlas extends Klas("", "", -1, Array.empty[String], Array.empty[Meth], Array.empty[Call]) { override def toString = "Klas()" }

class KlasExtractor private () extends asm.ClassVisitor(ASM5) {
  private[this] var myKlas: Klas = NoKlas
  private[this] var myMeths: List[V[Meth]] = Nil
  private[this] var myCalls: List[V[Call]] = Nil
  def from(cr: asm.ClassReader): Either[String, Klas] = {
    Try{ cr.accept(this, 0) } match {
      case Failure(t) => Left(t.toString + ": " + Option(t.getMessage).getOrElse("") + "\n" + t.getStackTrace.map("  "+_).mkString("\n"))
      case Success(_) => Right(myKlas)
    }
  }
  
  object MethExtractor extends asm.MethodVisitor(ASM5) {
    override def visitMethodInsn(op: Int, owner: String, name: String, desc: String, itf: Boolean) {
      myCalls = V(Call(op, owner, Array(name, desc))) :: myCalls
    }
  }
  
  override def visit(ver: Int, acc: Int, name: String, sig: String, sup: String, iface: Array[String]) {
    myKlas = myKlas.copy(name = name, sig = sig, access = acc, parents = if (iface.isEmpty) Array(sup) else sup +: iface)
  }
  override def visitSource(src: String, dbg: String) {}
  override def visitOuterClass(owner: String, name: String, desc: String) {}
  override def visitAnnotation(desc: String, vis: Boolean) = null
  override def visitAttribute(attr: asm.Attribute) {}
  override def visitInnerClass(name: String, outName: String, inName: String, acc: Int) {}
  override def visitField(acc: Int, name: String, desc: String, sig: String, v: Object) = null
  override def visitMethod(acc: Int, name: String, desc: String, sig: String, exc: Array[String]) = {
    myMeths = V(Meth(name, Array(sig))) :: myMeths
    MethExtractor
  }
  override def visitEnd {
    myKlas = myKlas.copy(methods = myMeths.reverseMap(_.value).toArray, calls = myCalls.reverseMap(_.value).toArray)
  }
}
object KlasExtractor {
  def apply(cr: asm.ClassReader) = (new KlasExtractor).from(cr)
}

class Usage {
}

object Usage {
  def apply(b: Array[Byte]) = KlasExtractor(new asm.ClassReader(b))
  def apply(s: String) = KlasExtractor(new asm.ClassReader(s))
}