package usage

import scala.util._
import scala.collection.mutable.{ AnyRefMap => RMap }
import scalax.collection.mutable.Graph
import scalax.collection.GraphPredef._
import scalax.collection.GraphEdge._
import org.objectweb.asm
import asm.Opcodes._

import scala.language.implicitConversions

trait Named { def name: String }

// Mini mutable option-like thingy
final class V[A >: Null <: AnyRef](private var myValue: A) {
  def isSet: Boolean = myValue ne null
  
  def value: A = 
    if (isSet) myValue
    else throw new NoSuchElementException("empty V")
  def valueOr[B >: A](default: => B) = if (isSet) myValue else default
  def evalOr[B](default: => B)(f: A => B) = 
    if (isSet) f(myValue) else default
  def orEmpty[B](implicit cbf: collection.generic.CanBuildFrom[A,B,A]) = if (isSet) myValue else cbf().result
  def evalOrEmpty[B,C](f: A => B)(implicit cbf: collection.generic.CanBuildFrom[B,C,B]) =
    if (isSet) f(myValue) else cbf().result

  def value(newValue: A): this.type = {
    myValue = newValue
    this
  }
  def xform(f: A => A): this.type = {
    if (isSet) myValue = f(myValue)
    this
  }
  def offer(value: A): this.type = {
    if (!isSet) myValue = value
    this
  }
  def unset: this.type = {
    myValue = null
    this
  }
  def identicalTo(value: A) = value eq myValue
  def foreach[U](f: A => U) { if (isSet) f(myValue) }
  def doIf[U](p: A => Boolean)(f: A => U) { if (isSet && p(myValue)) f(myValue) }
  def exists(p: A => Boolean) = isSet && p(myValue)
  def toV: this.type = this
  def toOption = if (isSet) Some(myValue) else None  
  
  @inline private[this] def vstr = myValue match { case n: Named => n.name; case x => x.toString }
  @inline private[this] def vhcode = myValue match { case n: Named => n.name.hashCode; case x => x.## }
  override def toString = if (isSet) "{" + vstr + "}" else "<>"
  override def hashCode = if (isSet) vhcode else "<>".hashCode
}
object V {
  def apply[A >: Null <: AnyRef](): V[A] = new V(null)
  def apply[A >: Null <: AnyRef](value: A): V[A] = new V(value)
  implicit def OptionToV[A >: Null <: AnyRef](oa: Option[A]): V[A] = new V(oa.orNull)
}
  

case class Call(op: Int, name: String, owner: String, desc: String, in: V[Meth]) extends Named {
  lazy val id = name + ".." + desc
  def str(from: Meth) = s"Call($op, $name, $owner, $desc, ${if (in identicalTo from) "^" else in.toString})"
  override def toString = str(null)
}
object NoCall extends Call(-1, "", "", "", V(NoMeth)) { override def toString = "Call()" }

case class Meth(name: String, access: Int, params: String, generic: Option[String], in: V[Klas]) extends Named {
  val wraps = V[Call]()
  val implemented = false
  lazy val id = name + ".." + params
  def isStatic = (access & ACC_STATIC) != 0
  def protection = (access & (ACC_PUBLIC | ACC_PROTECTED | ACC_PRIVATE)) match {
    case ACC_PUBLIC => -1
    case ACC_PROTECTED => 0
    case ACC_PRIVATE => 1
    case x => throw new Exception("What kind of access is " + x.toHexString + "?")
  }
  def str(from: Klas) = s"Meth($name,, $params,, ${generic.getOrElse("")},, ${if (in identicalTo from) "^" else in.toString})"
  override def toString = str(null)
}
object NoMeth extends Meth("", -1, "", None, V()) { override def toString = "Meth()" }

case class Klas(name: String, sig: String, access: Int, parents: Array[String]) extends Named {
  val fields = V[Array[String]]()
  val methods = V[Array[Meth]]()
  val calls = V[Array[Call]]()
  val comrades = V[List[Klas]]()  // Not even an empty list until we know it has no comrades
  def isSingle = fields.exists(_ contains "MODULE$")
  def isTrait = (access & ACC_INTERFACE) != 0
  def isImpl = name.endsWith("$class") && isAbstract && !methods.exists(_.exists(! _.isStatic))
  def isAbstract = (access & ACC_ABSTRACT) != 0
  def isFinal = (access & ACC_FINAL) != 0
  private[this] def parentString = parents.mkString(", ")
  private[this] def fieldsString = fields.evalOr("")(_.mkString(", "))
  private[this] def methodsString = methods.evalOr("")(_.map(_.str(this)).mkString(", "))
  private[this] def callsString = calls.evalOr("")(_.mkString(", "))
  override def toString = s"Klas($name, $sig, $access,, $parentString,, $fieldsString,, $methodsString,, $callsString)"
}
object NoKlas extends Klas("", "", -1, Array.empty[String]) { override def toString = "Klas()" }

class KlasExtractor private (listen: Call => Boolean) extends asm.ClassVisitor(ASM5) {
  private[this] val myKlas: V[Klas] = V()
  private[this] var myMeths: List[V[Meth]] = Nil
  private[this] var myCalls: List[V[Call]] = Nil
  private[this] var myFields: List[String] = Nil
  def from(cr: asm.ClassReader): Either[String, Klas] = {
    Try{ cr.accept(this, 0) } match {
      case Failure(t) => Left(Usage.explain(t))
      case Success(_) => Right(myKlas.value)
    }
  }
  
  private[this] object MethExtractor extends asm.MethodVisitor(ASM5) {
    var wraps = V[Call]()
    override def visitFieldInsn(op: Int, owner: String, name: String, desc: String) { wraps = None }
    override def visitIincInsn(v: Int, i: Int) { wraps = None }
    override def visitInsn(op: Int) {}
    override def visitIntInsn(op: Int, i: Int) {}
    override def visitInvokeDynamicInsn(name: String, desc: String, bsm: asm.Handle, bsmArgs: Object*) { wraps = None }
    override def visitJumpInsn(op: Int, l: asm.Label) { wraps = None }
    override def visitLdcInsn(cst: Object) {}
    override def visitLookupSwitchInsn(default: asm.Label, keys: Array[Int], labels: Array[asm.Label]) { wraps = None }
    override def visitMultiANewArrayInsn(desc: String, d: Int) { wraps = None }
    override def visitMethodInsn(op: Int, owner: String, name: String, desc: String, itf: Boolean) {
      val c = Call(op, name, owner, desc, myMeths.head)
      if (listen(c)) {
        myCalls = V(c) :: myCalls
        if (wraps == null) wraps = Some(c)
        else wraps = None
      }
    }
    override def visitTableSwitchInsn(i0: Int, i1: Int, default: asm.Label, labels: asm.Label*) { wraps = None }
    override def visitTypeInsn(op: Int, tpe: String) {}
    override def visitVarInsn(op: Int, v: Int) {}
    override def visitEnd() { wraps.doIf(_ ne NoCall)(c => myMeths.head.foreach(_.wraps.offer(c))) }
    def apply() = { wraps.unset; this: asm.MethodVisitor }
  }
  
  override def visit(ver: Int, acc: Int, name: String, sig: String, sup: String, iface: Array[String]) {
    myKlas.value( Klas(name, sig, acc, if (iface.isEmpty) Array(sup) else sup +: iface) )
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
    myMeths = V(Meth(name, acc, desc, Option(sig), myKlas)) :: myMeths
    MethExtractor()
  }
  override def visitEnd {
    myKlas.foreach{ k =>
      k.fields.offer(myFields.toArray.reverse)
      k.methods.offer(myMeths.reverseMap(_.value).toArray)
      k.calls.offer(myCalls.reverseMap(_.value).toArray)
    }
  }
}
object KlasExtractor {
  def apply(cr: asm.ClassReader, listen: Call => Boolean): Either[String, Klas] = (new KlasExtractor(listen)).from(cr)
  def apply(cr: asm.ClassReader): Either[String, Klas] = apply(cr, (c: Call) => true)
  
  def apply(is: java.io.InputStream, listen: Call => Boolean): Either[String, Klas] = apply(new asm.ClassReader(is), listen)
  def apply(b: Array[Byte], listen: Call => Boolean): Either[String, Klas] = apply(new asm.ClassReader(b), listen)
  def apply(s: String, listen: Call => Boolean): Either[String, Klas] = apply(new asm.ClassReader(s), listen)
  
  def apply(is: java.io.InputStream): Either[String, Klas] = apply(is, (c: Call) => true)
  def apply(b: Array[Byte]): Either[String, Klas] = apply(b, (c: Call) => true)
  def apply(s: String): Either[String, Klas] = apply(s, (c: Call) => true)
}

class Lib(val file: java.io.File, val klases: Array[Klas], val stdlib: Option[Lib]) { self =>
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
    lazy val ancestry: Map[String, Array[List[Meth]]] = {
      lookup.map{ case (k,v) => k -> {
        var order = 0L
        def nID = { order += 1; order }
        val included = new RMap[String, (Long, List[Meth])]
        if (extended.ancestors(v)) {
          extended.ancestors.get(v).outerNodeTraverser.foreach(_.methods.foreach(_.foreach{ pm =>
            if (!pm.isStatic) {
              included getOrNull pm.id match {
                case null => included += pm.id -> (nID -> (pm :: Nil))
                case (id, ms) => included += pm.id -> (id -> (pm :: ms))
              }
            }
          }))
        }
        else v.methods.valueOr(Array()).filter(! _.isStatic).foreach( m => included += m.id -> (nID -> (m :: Nil)) )
        included.map(_._2).toArray.sortBy(_._1).map{ case (_, ms) => if (ms.lengthCompare(1) > 0) ms.reverse else ms }
      }}
    }
    lazy val offspring: Map[Klas, Array[(Meth, List[Klas])]] = {
      lookup.collect{ case (_,v) if extended.descendants(v) => v -> {
        val myIds = v.methods.evalOrEmpty(_.map(_.id).toSet)
        val myLst = new RMap[String, List[Klas]]
        extended.descendants.get(v).outerNodeTraverser.filter(_.name != v.name).foreach{ cv =>
          val descIds = cv.methods.evalOrEmpty(_.map(_.id).toSet)
          (descIds & myIds).foreach{ name =>
            myLst getOrNull name match {
              case null => myLst += name -> (cv :: Nil)
              case xs   => myLst += name -> (cv :: xs)
            }
          }
        }
        val idM = v.methods.evalOrEmpty(_.map(x => x.id -> x).toMap)
        myLst.toArray.map{ case (s, xs) => idM(s) -> xs }
      }}
    }
    lazy val callgraph: Map[String, Map[Meth, Int]] = {
      val cg = new RMap[String, RMap[Meth, Int]]
      val relevant = stdlib.
        map(std => (c: Call) => lookup.contains(c.owner) || std.lookup.contains(c.owner)).
        getOrElse((c: Call) => lookup contains c.owner)
      klases.
        flatMap(_.calls.evalOrEmpty(_.filter(relevant).map(c => (c.owner + ".." + c.id) -> c))).
        groupBy(x => (x._1, x._2.in.value.id)).
        foreach{ case ((oid, _), xs) =>
          val m = xs.head._2.in.value
          cg getOrNull oid match {
            case null => cg += oid -> RMap(m -> xs.length)
            case rmap =>
              if (rmap contains m) rmap += m -> (rmap(m) + xs.length)  // Shouldn't ever hit this!
              else rmap += m -> xs.length
              // Side-effecting, so we're done
          }
        }
        // Side-effecting, so we're done
      cg.map{ case (k,v) => k -> v.toMap }.toMap
    }
  }
  def upstream(s: String) = lookup.get(s).flatMap(x => Try{ ancestors.get(x).outerNodeTraverser.toArray }.toOption )
  def downstream(s: String) = lookup.get(s).flatMap(x => Try { descendants.get(x).outerNodeTraverser.toArray }.toOption )
  def alike(s: String) = lookup.get(s).flatMap(x => Try { relatives.get(x).outerNodeTraverser.toArray }.toOption )
}
object Lib {
  def read(f: java.io.File, lib: Option[Lib], listen: Call => Boolean = _ => true): Either[Vector[String], Lib] = {
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
            Try{ KlasExtractor(zf.getInputStream(ze), listen) match {
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
      if (problems.length > 0) Left(problems) else Right(new Lib(f, ks.result, lib))
    } match {
      case Success(x) => x
      case Failure(t) => Left(Vector("Problem reading source library " + f.getCanonicalFile.getPath, Usage.explain(t)))
    }
  }
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
  
  def explain(t: java.lang.Throwable) = 
    t.toString + ": " + Option(t.getMessage).getOrElse("") + "\n" + t.getStackTrace.map("  "+_).mkString("\n")
}
