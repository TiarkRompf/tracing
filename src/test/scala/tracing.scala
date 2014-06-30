package tracing

import scala.language.implicitConversions

import java.io._
import scala.collection._

/*

DONE:

+ 1 meta-layer (low-level interprets high-level)

+ n meta-layers (low-level interprets high-level, interprets high-level, ...)

TODO:

- proper profiling

- optimize traces: cse, scalarize field access, materialize writes on guard fail
    - question: aliasing for heap fields ?

*/


/* ---------- PART 1: low-level execution ---------- */

trait Syntax {
  def pretty(e: Any): String

  case class Block(stms: List[Stm], cont: Jump) {
    override def toString = {
      "{\n" + stms.map(pretty(_) +"\n").mkString("")+pretty(cont) + "\n}"
    }
  }

  abstract class Jump
  case class IfElse(c: Exp, a: Jump, b: Jump) extends Jump
  case class Goto(name: Exp) extends Jump
  case object Done extends Jump

  case class Guard(name: Exp, cmp: String, block: Block) extends Jump

  abstract class Stm
  case class New(a: Exp, b: Exp) extends Stm  // a[b] := new
  case class Put(a: Exp, b: Exp, c: Exp) extends Stm  // a[b] := c
  case class Print(a: Exp) extends Stm
  case class Output(a: Exp) extends Stm

  abstract class Exp
  case class Const(x: Any) extends Exp {
    override def toString = {
      s"Const(${x.toString.take(10)})"
    }
  }
  case class Rec(x: List[(String,Exp)]) extends Exp // TODO: express as alloc + puts
  case class Plus(x: Exp, y: Exp) extends Exp
  case class Minus(x: Exp, y: Exp) extends Exp
  case class Times(x: Exp, y: Exp) extends Exp
  case class Equal(x: Exp, y: Exp) extends Exp
  case class LessThan(x: Exp, y: Exp) extends Exp
  case class ITE(c: Exp, x: Exp, y: Exp) extends Exp
  case class Get(a: Exp, b: Exp) extends Exp  // a[b]
  case object Mem extends Exp
}

trait Print extends Syntax {
  def pretty(e: Any): String = e match {
    case Mem => "mem"
    case c:String => '"'+c+'"'
    case Const(c:String) => '"'+c+'"'
    case Const(c) => c.toString
    case Get(a,b) => s"${pretty(a)}[${pretty(b)}]"
    case Equal(a,b) => s"${pretty(a)} == ${pretty(b)}"
    case LessThan(a,b) => s"${pretty(a)} <= ${pretty(b)}"
    case ITE(c,a,b) => s"if (${pretty(c)}) ${pretty(a)} else ${pretty(b)}"
    case Rec(xs) => s"Rec(${xs.map(p=>p._1 + "->"+pretty(p._2)).mkString(",")})"
    case Plus(a,b) => s"${pretty(a)} + ${pretty(b)}"
    case Minus(a,b) => s"${pretty(a)} + ${pretty(b)}"
    case Times(a,b) => s"${pretty(a)} * ${pretty(b)}"

    case New(a,b) => s"${pretty(a)}[${pretty(b)}] = new"
    case Put(a,b,c) => s"${pretty(a)}[${pretty(b)}] = ${pretty(c)}"
    case Print(a) => s"print(${pretty(a)})"
    case Output(a) => s"output(${pretty(a)})"

    case IfElse(c,a,b) => s"if (${pretty(c)}) ${pretty(a)} else ${pretty(b)}"
    case Goto(a) => s"goto ${pretty(a)}"
    case Done => "exit"

    case Guard(name, cmp, block) => s"guard ${pretty(name)} == ${pretty(cmp)} ${pretty(block)}}"

    case e => e.toString
  }
}


trait Eval extends Syntax with Print {
  type Label = String
  type Obj = mutable.Map[Any,Any]

  val prog = mutable.Map[Label,Block]()

  var trace: Vector[String] = Vector.empty
  val mem: Obj = mutable.Map()

  def ev(e: Exp): Any = try { e match {
    case Mem => mem
    case Const(c) => c
    case Get(a,b) => (eval[Obj](a))(ev(b))
    case Equal(a,b) => ev(a) == ev(b)
    case LessThan(a,b) => eval[Int](a) <= eval[Int](b)
    case ITE(c,a,b) => if (eval[Boolean](c)) ev(a) else ev(b)
    case Plus(a,b) => eval[Int](a) + eval[Int](b)
    case Minus(a,b) => eval[Int](a) - eval[Int](b)
    case Times(a,b) => eval[Int](a) * eval[Int](b)
    case Rec(as) => mutable.Map() ++= as.map(p=> (p._1,ev(p._2)))
  }} catch {
    case ex =>
      println(s"error in ev(${pretty(e)}): $ex")
      e match {
        case Get(a,b) => println(eval[Obj](a))
        case _ =>
      }
      throw ex
  }

  def eval[T](e: Exp): T = ev(e).asInstanceOf[T]

  abstract class Trampoline
  case object TrampoDone extends Trampoline
  case class TrampoLabel(l: Label) extends Trampoline
  case class TrampoBlock(b: Block) extends Trampoline

  def exec(name: Label): Unit = try {
    trace = trace :+ name
    //println("0: "+name)
    exec(prog(name))
  } catch {
    case ex =>
      println(s"error in ex(${pretty(prog(name))}): $ex")
      throw ex
  }
  @scala.annotation.tailrec
  final def exec(block: Block): Unit = {
    block.stms.foreach(exec);
    resolve(block.cont) match {
      case TrampoDone =>
      case TrampoLabel(name) =>
        trace = trace :+ name
        //println("0: "+name)
        exec(prog(name))
      case TrampoBlock(block) =>
        exec(block)
    }
  }
  def resolve(jump: Jump): Trampoline = jump match {
    case Done => TrampoDone
    case Goto(l) =>
      TrampoLabel(eval[Label](l))
    case IfElse(c,a,b) => if (eval[Boolean](c)) resolve(a) else resolve(b)
    case Guard(l,x,b) =>
      val x1 = eval[Label](l)
      if (x1 == x) TrampoBlock(b)
      else TrampoLabel(x1)
  }
  def exec(stm: Stm): Unit = { /*println(stm);*/ stm } match {
    case Print(a) => println(eval[Any](a))
    case Output(a) => output(eval[Any](a))
    case Put(a,b,c) => (eval[Obj](a))(eval[Any](b)) = eval[Any](c)
    case New(a,b) => (eval[Obj](a))(eval[Any](b)) = new mutable.HashMap
  }
  var out: Any = null
  def output(a: Any): Unit = {
    //println("OUT:"+a)
    out = a
  }

  def merge(l1: Label, l2: Label) = {

    val b2 = prog(l2)

    def merge0(b1: Block): Block = {
      val Block(stms,jmp) = merge1(b1.cont)
      Block(b1.stms++stms, jmp)
    }
    def merge1(b1: Jump): Block = b1 match {
      case Goto(Const(`l2`)) => b2 // optimize guard if always true!
      case Goto(t1) => Block(Nil,Guard(t1,l2,b2))
      case Guard(tx,lx,bx) => Block(Nil,Guard(tx,lx,merge0(bx)))
    }

    val b1 = prog(l1)
    prog(l1) = merge0(b1)

  }

  def mergeAll(ls: List[Label]) =
    if (ls.nonEmpty) for (l2 <- ls.tail) merge(ls.head,l2)
}

trait LowLevel extends Syntax with Eval with Print

/* ---------- PART 2: high-level embedded language ---------- */

trait Lang {
  abstract class P[A,B] {
    def f: Fun[A,B]
    def a: Rep[A]
    def b: Rep[B]
  }

  type Rep[+T]

  type Fun[A,B]

  def unit: Rep[Unit] = lift(())
  def begin[T](a: => Any, b: => Rep[T]): Rep[T] = {
    a;b
  }
  def begin[T](a: => Any, b: => Any, c: => Rep[T]): Rep[T] = {
    a;b;c
  }
  def begin[T](a: => Any, b: => Any, c: => Any, d: => Rep[T]): Rep[T] = {
    a;b;c;d
  }
  def begin[T](a: => Any, b: => Any, c: => Any, d: => Any, e: => Rep[T]): Rep[T] = {
    a;b;c;d;e
  }
  type Arr[A]
  def newMyArr[A]: Rep[Unit]
  def myArr[A]: Arr[A]
  implicit class ArrayOps[A](a: Arr[A]) {
    def apply(i:Rep[Int]): Rep[A] = arr_apply(a, i)
    def update(i:Rep[Int],v:Rep[A]): Rep[Unit] = arr_update(a, i, v)
  }
  def arr_apply[A](a: Arr[A], i: Rep[Int]): Rep[A]
  def arr_update[A](a: Arr[A], i: Rep[Int], v: Rep[A]): Rep[Unit]

  implicit class FunOps[A,B](f:Fun[A,B]) {
    def apply(x:Rep[A]):Rep[B] = fun_apply(f,x)
  }
  def fun[A,B](name: String)(f: Rep[A]=>Rep[B]): Fun[A,B]
  def fun_apply[A,B](f:Fun[A,B],x:Rep[A]): Rep[B]

  implicit def lift[T](x: T): Rep[T]

  implicit class IntOps(x: Rep[Int]) {
    def ===(y: Rep[Int]) = int_equ(x,y)
    def <=(y: Rep[Int]) = int_lte(x,y)
    def +(y: Rep[Int]) = int_plus(x,y)
    def -(y: Rep[Int]) = int_minus(x,y)
    def *(y: Rep[Int]) = int_times(x,y)
  }

  implicit class BoolOps(x: Rep[Boolean]) {
    def ||(y: Rep[Boolean]): Rep[Boolean] = if (x) true else y
  }

  def int_equ(x:Rep[Int],y:Rep[Int]): Rep[Boolean]
  def int_lte(x:Rep[Int],y:Rep[Int]): Rep[Boolean]
  def int_plus(x:Rep[Int],y:Rep[Int]): Rep[Int]
  def int_minus(x:Rep[Int],y:Rep[Int]): Rep[Int]
  def int_times(x:Rep[Int],y:Rep[Int]): Rep[Int]

  def __ifThenElse[T](c: Boolean, a: => T, b: => T): T = c match { case true => a case false => b }
  def __ifThenElse[T](c: Rep[Boolean], a: => Rep[T], b: => Rep[T]): Rep[T]

  def str_equ(x:Rep[String],y:Rep[String]):Rep[Boolean]

  def pair(x: Rep[Any], y: Rep[Any]): Rep[Any]
  def fst[A](t: Rep[Any]): Rep[A]
  def snd[A](t: Rep[Any]): Rep[A]
}

trait LangX extends Lang {
  type Term

  def iprint(n:Int, x: Rep[Any]): Rep[Unit]

  def newArr[A](name: String): Rep[Unit]
  def getArr[A](name: String): Arr[A]
  override def newMyArr[A]: Rep[Unit] = newArr[A]("my_only_array")
  override def myArr[A]: Arr[A] = getArr[A]("my_only_array")

  type Fun2[A,B,C]
  implicit class Fun2Ops[A,B,C](f:Fun2[A,B,C]) {
    def apply(x1:Rep[A],x2:Rep[B]):Rep[C] = fun2_apply(f,x1,x2)
  }
  def fun2[A,B,C](name: String)(f: (Rep[A],Rep[B])=>Rep[C]): Fun2[A,B,C]
  def fun2_apply[A,B,C](f:Fun2[A,B,C],x:Rep[A],x2:Rep[B]):Rep[C]

  def record(xs: (String,Rep[Any])*): Rep[Term]
  def field(x: Rep[Term], k: String): Rep[Term]

  override def pair(x: Rep[Any], y: Rep[Any]): Rep[Any] = record("fst"->x, "snd"->y)
  override def fst[A](t: Rep[Any]): Rep[A] = field(t.asInstanceOf[Rep[Term]], "fst").asInstanceOf[Rep[A]]
  override def snd[A](t: Rep[Any]): Rep[A] = field(t.asInstanceOf[Rep[Term]], "snd").asInstanceOf[Rep[A]]
}

// direct execution

trait LangDirect extends LangX {
  type Val[+T] = Rep[T]

  case class Rep[+T](x:T)

  def iprint(n: Int, x: Rep[Any]) = println(s"$n: " + x.x)

  var arrays = mutable.Map[String,Arr[_]]()
  type Arr[A] = Rep[mutable.Map[Int,A]]
  def newArr[A](name: String): Rep[Unit] = {
    val a:Arr[A] = Rep(mutable.Map())
    arrays(name) = a
    ()
  }
  def getArr[A](name: String): Arr[A] = arrays(name).asInstanceOf[Arr[A]]
  def arr_apply[A](a: Arr[A], i: Rep[Int]): Rep[A] = a.x(i.x)
  def arr_update[A](a: Arr[A], i: Rep[Int], v: Rep[A]): Rep[Unit] = {a.x(i.x) = v.x; ()}

  case class Fun[A,B](f: Rep[A]=>Rep[B])
  case class Fun2[A,B,C](f: (Rep[A],Rep[B])=>Rep[C])

  def fun[A,B](name: String)(f: Val[A]=>Val[B]): Fun[A,B] = Fun(f)
  def fun2[A,B,C](name: String)(f: (Val[A],Val[B])=>Val[C]): Fun2[A,B,C] = Fun2(f)

  def fun_apply[A,B](f:Fun[A,B],x:Rep[A]):Rep[B] = f.f(x.x)
  def fun2_apply[A,B,C](f:Fun2[A,B,C],x:Rep[A],x2:Rep[B]):Rep[C] = f.f(x.x, x2.x)

  def __ifThenElse[A](c: Rep[Boolean], a: => Val[A], b: => Val[A]): Val[A] = if (c.x) a else b

  implicit def lift[T](x: T) = Rep(x)

  def int_equ(x:Rep[Int],y:Rep[Int]):Rep[Boolean] = Rep(x.x == y.x)
  def int_lte(x:Rep[Int],y:Rep[Int]):Rep[Boolean] = Rep(x.x <= y.x)
  def int_plus(x:Rep[Int],y:Rep[Int]):Rep[Int] = Rep(x.x + y.x)
  def int_minus(x:Rep[Int],y:Rep[Int]):Rep[Int] = Rep(x.x - y.x)
  def int_times(x:Rep[Int],y:Rep[Int]):Rep[Int] = Rep(x.x * y.x)

  def str_equ(x:Rep[String],y:Rep[String]):Rep[Boolean] = Rep(x.x == y.x)

  type Term = Map[String,Rep[Any]]

  def record(xs: (String,Rep[Any])*): Rep[Term] = Rep(Map() ++ xs)
  def field(x: Rep[Term], k: String): Rep[Term] = x.x.get(k) match {
    case Some(v) => v.asInstanceOf[Rep[Term]]
    case None => throw new NoSuchElementException("key not found: "+k+" in "+x)
  }
}

// translation to low-level target

trait LangLowLevel extends LangX with LowLevel {
  var label = "main"
  var stms: List[Stm] = Nil

  type Term = Any
  type Val[+T] = Exp
  type Rep[+T] = Exp

  def iprint(n: Int, x: Rep[Any]) = {
    stms = stms :+ Print(x) // FIXME: level
  }

  type Arr[A] = Exp
  def newArr[A](name: String) = {
    stms = stms :+ New(Mem, name)
    Const(0)
  }
  def getArr[A](name: String) = {
    Get(Mem, name)
  }
  def arr_apply[A](a: Arr[A], i: Rep[Int]): Rep[A] = {
    Get(a, i)
  }
  def arr_update[A](a: Arr[A], i: Rep[Int], v: Rep[A]): Rep[Unit] = {
    stms = stms :+ Put(a, i, v)
    Const(0)
  }

  implicit def lift(x: Int): Exp = Const(x)
  implicit def lifts(x: String): Exp = Const(x)

  case class Fun[A,B](name: String, f: Val[A]=>Val[B])

  def fun_apply[A,B](f:Fun[A,B],x:Val[A]) = {
    val uname = label+"-"+f.name
    val ucont = uname
    val ures  = uname

    val sd = Get(Mem,"sd")
    val sd1 = Plus(sd,1)
    val sp = Get(Mem,"sp")
    val fp = Get(sp,sd)
    val fp1 = Get(sp,sd1)
    stms = stms :+ New(sp,sd1)
    stms = stms :+ Put(fp1, "arg",x)
    stms = stms :+ Put(fp1, "ret",ucont)
    stms = stms :+ Put(Mem, "sd", sd1)
    prog(label) = Block(stms, Goto(f.name))

    label = ucont
    stms = Nil
    stms = stms :+ Put(Mem, "sd",Minus(sd,1))
    stms = stms :+ Put(fp, ures,Get(fp1,"res"))
    stms = stms :+ Put(sp,sd1,"null")
    Get(fp,ures)
  }

  def fun[A,B](name: String)(f: Val[A]=>Val[B]): Fun[A,B] = {
    if (!prog.contains(name)) {
      val label0 = label
      val stms0 = stms

      label = name
      stms = Nil
      prog(label) = Block(Nil,Done)

      val sd = Get(Mem,"sd")
      val fp = Get(Get(Mem,"sp"),sd)

      val res = f(Get(fp,"arg"))
      stms = stms :+ Put(fp,"res",res)

      prog(label) = Block(stms,Goto(Get(fp,"ret")))

      label = label0
      stms = stms0
    }
    Fun(name, f)
  }

  type Fun2[A,B,C] = Fun[Term,C]

  def fun2[A,B,C](name: String)(f: (Val[A],Val[B])=>Val[C]): Fun2[A,B,C] = {
    fun(name) { x: Rep[Term] =>
      f(field(x,"1").asInstanceOf[Rep[A]],
        field(x,"2").asInstanceOf[Rep[B]])
    }
  }


  def fun2_apply[A,B,C](f:Fun2[A,B,C],x:Val[A],x2:Val[B]) = {
    fun_apply(f,Rec(List("1" -> x, "2" -> x2)))
  }


  def __ifThenElse[A](c: Val[Boolean], a: => Val[A], b: => Val[A]): Val[A] = {

    val uname = label+"-if"
    val uthen = uname+"t"
    val uelse = uname+"e"
    val ucont = uname
    val ures  = uname

    prog(label) = Block(stms, IfElse(c,Goto(uthen),Goto(uelse)))

    val sd = Get(Mem,"sd")
    val sp = Get(Mem,"sp")
    val fp = Get(sp,sd)

    label = uthen
    stms = Nil
    val x = a
    stms = stms :+ Put(fp,ures,x)
    prog(label) = Block(stms, Goto(ucont))

    label = uelse
    stms = Nil
    val y = b
    stms = stms :+ Put(fp,ures,y)
    prog(label) = Block(stms, Goto(ucont))

    label = ucont
    stms = Nil
    Get(fp,ures)
  }

  implicit def lift[T](x: T) = Const(x)

  def int_equ(x:Rep[Int],y:Rep[Int]):Rep[Boolean] = Equal(x,y)
  def int_lte(x:Rep[Int],y:Rep[Int]):Rep[Boolean] = LessThan(x,y)
  def int_plus(x:Rep[Int],y:Rep[Int]):Rep[Int] = Plus(x,y)
  def int_minus(x:Rep[Int],y:Rep[Int]):Rep[Int] = Minus(x,y)
  def int_times(x:Rep[Int],y:Rep[Int]):Rep[Int] = Times(x,y)

  def str_equ(x:Rep[String],y:Rep[String]):Rep[Boolean] = Equal(x,y)

  def record(xs: (String,Rep[Any])*): Rep[Term] = {
    //val hd = Get(Mem,"hd")
    //val hp = Get(Mem,"hp")
    //stms = stms :+ Put(Mem, "hd",Plus(sd,1))
    Rec(xs.toList)
  }

  def field(x: Rep[Term], k: String): Rep[Term] = Get(x,k)
}

trait RunLowLevel extends LangLowLevel {

  def runLow[A,B](f: => Fun[A,B], arg: => Any) = {
    prog.clear

    val res = f(Get(Mem,Const("in")))
    stms = stms :+ Output(res)
    prog(label) = Block(stms, Done)

    trace = Vector.empty
    mem.clear
    mem("in") = arg
    mem("sd") = 0
    mem("sp") = mutable.Map(0 -> mutable.Map())

    //mem("hd") = 0
    //mem("hp") = mutable.Map()

    //println(prog)

    //println("---")

    exec("main")

    //println("---")

    //mem foreach println
  }
}

/* ---------- PART 3: profiling etc (currently out of order ...) ---------- */

trait Analyze extends RunLowLevel {
  val verbose = false

  class GraphPrinter(s1: String) {
    // export graph viz
    val dir = new File(s"graphs-$s1")
    dir.mkdirs
    dir.listFiles.foreach(_.delete)
    val combinedPdf = new File(s"graphs-all-$s1.pdf")
    if (combinedPdf.exists) combinedPdf.delete

    def printGraph(s2:String)(mergeHist: Int=>Seq[Int],maxloopcount:Int=>Int, freq: Map[Int,Int], edgefreq: Map[(Int,Int),Int], edgehopfreq: Map[(Int,Int),Int])(edges: Seq[(Int,Int)]): Unit = {
      val out = new PrintStream(new File(dir,s"g$s2.dot"))
      out.println("digraph G {")
      //out.println("rankdir=LR")

      /*out.println("""struct1 [shape=plaintext label=<<TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0" CELLPADDING="4"><TR><TD>""")
      out.println("foo1<BR/>")
      out.println("foo2<BR/>")
      out.println("foo3<BR/>")
      out.println("""</TD></TR></TABLE>>];""")*/

      val fmax = freq.values.max
      val pmax = 15
      def scale(f: Double) = if (fmax <= pmax) f else f/fmax * pmax
      val nodes = (edges.map(_._1)) //++ edges.map(_._2)).distinct
      for ((a,f) <- freq) {
        val fw = scale(f)
        val size = mergeHist(a).length
        val color = if (nodes contains a) "red" else "black"
        out.println(s"""L$a [label=\"B$a\\n s=$size f=$f\" weight="$f" color="$color" penwidth="${fw}" shape=box]""")
      }
      for (((a,b),f) <- edgefreq) {
        val fw = scale(f)
        val extra = if (a != b) "" else s"(max ${maxloopcount(a)})"
        val color = if (edges contains (a,b)) "red" else "black"
        out.println(s"""L$a -> L$b [label=\" $f $extra\" weight="$f" color="$color" penwidth="${fw}"]""")
      }
      /* draw edge hop frequences:  a -> ? -> b
      for (((a,b),f) <- edgehopfreq) {
        val fw = 0.5
        val extra = if (a != b) "" else s"(max ${maxloopcount(a)})"
        val color = "green"
        out.println(s"""L$a -> L$b [label=\"$f $extra\" weight="0" color="$color" penwidth="${fw}"]""")
      }*/    
      out.println("}")
      out.close()
      import scala.sys.process._
      s"dot -Tpdf -O $dir/g$s2.dot".!
    }

    def finish() = {
      // join all pdfs
      import scala.sys.process._
      (s"./pdfjoin.sh -o $combinedPdf " + 
        dir.listFiles.filter(_.getName.endsWith(".pdf")).mkString(" ")).!!
    }
  }


  def report(s1:String) = {
    // note: both steps can be run independently or together.
    val tr1 = analyzeDeterministicJumps(s1+"A")
    this.trace = tr1.map(_.toString)
    val tr2 = analyzeTraceHierarchies(s1+"B")
  }


  def indexToBlockFun[A:Manifest](t: Vector[A]) = t.distinct.toArray

  // first version: inline deterministic jumps
  def analyzeDeterministicJumps(s1:String): Vector[Int] = {
    val traceB = this.trace

    implicit class MySeqOps[T](xs: Seq[T]) {
      def collectBy[K,V](f1: T => K, f2: Seq[T] => V): Map[K,V] =
        xs.groupBy(f1).map(kv => (kv._1,f2(kv._2)))
    }

    // map blocks in trace to numeric indexes
    if (verbose) println("block <-> index:")
    val indexToBlock = indexToBlockFun(traceB)
    val blockToIndex = indexToBlock.zipWithIndex.toMap
    if (verbose) println(blockToIndex)

    var trace = traceB map blockToIndex

    // merge nodes
    var count = indexToBlock.length
    val mergeHist = new Array[Vector[Int]](10000)
    for (i <- 0 until mergeHist.length)
      mergeHist(i) = Vector(i)

    def merge(xs: List[Int]) = {
      val List(a,b) = xs
      mergeHist(a) = mergeHist(a) ++ mergeHist(b)
      val str0 = trace.mkString(";",";;",";")
      val str1 = str0.replaceAll(s";$a;;$b;",s";$a;")
      trace = str1.split(";").filterNot(_.isEmpty).map(_.toInt).toVector
      // if (verbose) println(trace)
    }
    def dup(xs: List[Int]) = {
      val List(a,b) = xs
      val c = count
      count += 1
      mergeHist(c) = mergeHist(b)
      val str0 = trace.mkString(";",";;",";")
      val str1 = str0.replaceAll(s";$a;;$b;",s";$a;;$c;")
      trace = str1.split(";").filterNot(_.isEmpty).map(_.toInt).toVector
      //println(trace)
    }

    // find max iteration count
    def maxloopcount(a: Int): Int = {
      var k = 0
      val str0 = trace.mkString(";",";;",";")
      var search = s";$a;"
      while (true) {
        if (!str0.contains(search)) return k
        k += 1
        search = search + s";$a;"
      }
      k
    }

    // export graph viz
    val gg = new GraphPrinter(s1)

    // perform one step of analysis/transformation
    def analyze(step: Int): Unit = {
      if (step > 500) return println("ABORT")
      println(s"/* analysis pass $step */")

      // compute frequencies, sort to find hotspots
      val freq = trace.collectBy(x=>x, _.length)
      println("hotspots:")
      val hotspots = freq.toSeq.sortBy(-_._2)
      hotspots.take(10).foreach(println)

      val hottest = hotspots.head
      if (verbose) {
        println("hottest")
        println(hottest)
        val curIndexToBlock = indexToBlockFun(trace)
        println(curIndexToBlock(hottest._1) + " -> " + hottest._2)
        println()
      }

      // compute hot edges / node pairs
      val edgefreq = (trace zip trace.drop(1)) collectBy(x=>x, _.length);
      println("hot edges:")
      val hotedges = edgefreq.toSeq.sortBy(-_._2)
      hotedges.take(10).foreach(println)
      println()

      if (verbose) {
        val hottestEdge = hotedges.head
        println("hottest")
        println(hottestEdge)
        println()
      }

      // compute hot node triples
      val edgetripfreq = (trace zip trace.drop(1) zip trace.drop(2)) collectBy(x=>(x._1._1,x._1._2,x._2), _.length);
      val edgehopfreq = (trace zip trace.drop(1) zip trace.drop(2)) collectBy(x=>(x._1._1,x._2), _.length);

      if (verbose) {
        println("hot edge triples:")
        val hotedgestrip = edgetripfreq.toSeq.sortBy(-_._2)
        hotedgestrip.take(10).foreach(println)
        println()

        println("hot edge hops:")
        val hotedgeshop = edgehopfreq.toSeq.sortBy(-_._2)
        hotedgeshop.take(10).foreach(println)
        println()
      }

      // compute pred/succ sets, specificity

      val pred = (trace zip trace.drop(1)) collectBy(_._2, _.map(_._1).distinct);
      val succ = (trace zip trace.drop(1)) collectBy(_._1, _.map(_._2).distinct);

      for ((h,_) <- hotspots.take(10)) {
        println(pred.getOrElse(h,Vector.empty) + " --> " + h + " --> " + succ.getOrElse(h,Vector.empty))
      }
      println()

      if (verbose) {
        for ((h,_) <- hotspots.take(10); ((a,`h`,b), f) <- edgetripfreq) {
          println(a + " --> " + h + " --> " + b + s" (f=$f)")
        }
        println()
      }

      val continueAnalyze: () => Nothing = { () => return analyze(step + 1) }

      /* 
      Trying two variants: (1) considers one node at a time in order
      of execution frequency, whereas (2) considers all jumps at once.

      The results seem to be about the same, but variant2 does 
      more work per step and converges faster.

      The main limitation (e.g. for pascal) is that only fully
      deterministic control transfers are inlined (i.e. A always 
      followed by B).

      In pascal, these are exhausted at some point.

      So we need a way to "disentangle" the control flow more.
      Looking at triples of nodes (AXB vs AYB) insted of just pairs
      is one idea.
      */

      /* 
      VARIANT 2: 
        Find all deterministic control transfers (node A always calls B)
        and inline them (unless B is a loop with > 2 iterations).
      */

      def variant2(): Unit = {
        def pred0(x: Int) = pred.getOrElse(x,Seq())
        def succ0(x: Int) = succ.getOrElse(x,Seq())

        val loopThresh = 3
        //val isoNodes = hotspots collect { case (h,f) if pred0(h) forall (p => succ(p).size == 1) => h }
        //val isoEdges = hotedges collect { case ((a,b),f) if isoNodes contains b => (a,b) } // only edge
        val isoNodes = hotspots collect { case (h,f) if !(succ0(h) contains h) || maxloopcount(h) <= loopThresh => h }
        val isoEdges = hotedges collect { case ((a,b),f) if succ(a).size == 1 && (isoNodes contains b) => (a,b) } // specific transfer

        gg.printGraph("%03d".format(step))(mergeHist,maxloopcount,freq,edgefreq,edgehopfreq)(isoEdges)

        val isoEdgesTopo = isoEdges.sortBy { case (a,b) => -a }

        for ((a,b) <- isoEdges)
          merge(List(a,b))
        if (isoEdges.nonEmpty)
          continueAnalyze()
      }

      /* 
      VARIANT 1: 
        Pick hottest node with largest outdegree B. Find callers A,
        who only call B. Inline B into A (unless B is a loop).
      */

      def variant1(): Unit = {
        val max = hotspots.length
        for (deg   <- max to 0 by -1; // outdegree
             (h,f) <- hotspots if pred contains h) {
          var hit: List[(Int,Int)] = Nil
          if (succ contains h) {
            // among the hottest hotspots, pick the one with the largest outdegree
            if (succ(h).size == deg) {
              // if it's a loop don't bother -- don't start peeling iterations
              if (!(succ(h) contains h)) {
                for (p <- pred(h) if succ(p).size == 1) {
                  println(s" -----> merge $p,$h")
                  if (p != h) {
                    merge(List(p,h))
                    hit = ((p,h))::hit
                  } else println("EEE")
                }
              }
            }
          }
          if (hit.nonEmpty) {
            println(hit)
            gg.printGraph("%03d".format(step))(mergeHist,maxloopcount,freq,edgefreq,edgehopfreq)(hit)
            continueAnalyze()
          }
        }
      }

      // unroll small loops -- may or may not want to do this
      def unrollSmallLoops(): Unit = {
        for ((h,f) <- hotspots if succ contains h) {
          if ((succ(h) contains h) && maxloopcount(h) <= 3) {
            println(s" -----> unroll $h,$h")
            merge(List(h,h))
            gg.printGraph("%03d".format(step))(mergeHist,maxloopcount,freq,edgefreq,edgehopfreq)(List((h,h)))
            continueAnalyze()
          }
        }
      }


      //unrollSmallLoops()
      variant2()

      // print final graph
      gg.printGraph("%03d".format(step))(mergeHist,maxloopcount,freq,edgefreq,edgehopfreq)(Nil)
    }

    try {
      analyze(0)
      if (verbose) {
        println()
        println("merge history:")
        mergeHist.filter(_.length > 1).foreach(println)
        println()
        println("final trace:")
        println(trace)
      }
      trace
    } finally {
      gg.finish()
    }
  }


  def analyzeTraceHierarchies(s1:String): Vector[Int] = {
    val traceB = this.trace

    implicit class MySeqOps[T](xs: Seq[T]) {
      def collectBy[K,V](f1: T => K, f2: Seq[T] => V): Map[K,V] =
        xs.groupBy(f1).map(kv => (kv._1,f2(kv._2)))
    }

    // map blocks in trace to numeric indexes
    if (verbose) println("block <-> index:")
    val indexToBlock = indexToBlockFun(traceB)
    val blockToIndex = indexToBlock.zipWithIndex.toMap
    if (verbose) println(blockToIndex)

    var trace = traceB map blockToIndex

    // merge nodes
    var count = indexToBlock.length
    val mergeHist = new Array[Vector[Int]](10000)
    for (i <- 0 until mergeHist.length)
      mergeHist(i) = Vector(i)

    def merge(xs: List[Int]) = {
      val List(a,b) = xs
      mergeHist(a) = mergeHist(a) ++ mergeHist(b)
      val str0 = trace.mkString(";",";;",";")
      val str1 = str0.replaceAll(s";$a;;$b;",s";$a;")
      trace = str1.split(";").filterNot(_.isEmpty).map(_.toInt).toVector
      // if (verbose) println(trace)
    }
    def dup(xs: List[Int]) = {
      val List(a,b) = xs
      val c = count
      count += 1
      mergeHist(c) = mergeHist(b)
      val str0 = trace.mkString(";",";;",";")
      val str1 = str0.replaceAll(s";$a;;$b;",s";$a;;$c;")
      trace = str1.split(";").filterNot(_.isEmpty).map(_.toInt).toVector
      //println(trace)
    }

    // find max iteration count
    def maxloopcount(a: Int): Int = {
      var k = 0
      val str0 = trace.mkString(";",";;",";")
      var search = s";$a;"
      while (true) {
        if (!str0.contains(search)) return k
        k += 1
        search = search + s";$a;"
      }
      k
    }

    val gg = new GraphPrinter(s1)

    def splitWhere[T](xs0: Seq[T])(f: T => Boolean): List[Seq[T]] = { 
      val buf = new scala.collection.mutable.ListBuffer[Seq[T]]
      var xs = xs0
      while (true) {
        val i = xs.indexWhere(f) 
        if (i < 0) {
          buf += xs
          return buf.result
        } else { 
          val (h,t) = xs.splitAt(i+1)
          buf += h
          xs = t
        } 
      }
      throw new Exception
    }
    assert(splitWhere(List(1,2,3,4,5,6,7,8,9))(_ % 4 == 0) == 
      List(List(1, 2, 3, 4), List(5, 6, 7, 8), List(9)))

    // perform one step of analysis/transformation
    def analyze(step: Int): Vector[Int] = {
      if (step > 30) {
        println("ABORT")
        return trace
      }
      println(s"/* analysis pass $step */")

      // compute frequencies, sort to find hotspots
      val freq = trace.collectBy(x=>x, _.length)
      println("hotspots:")
      val hotspots = freq.toSeq.sortBy(-_._2)
      hotspots.take(10).foreach(println)
      println

      //if (verbose) {
      if (!hotspots.isEmpty) {
        val hottest = hotspots.head
        println("hottest")
        println(hottest)
        val curIndexToBlock = indexToBlockFun(trace)
        println(curIndexToBlock(hottest._1) + " -> " + hottest._2)
        println()
      } else {
        println("NO hotspots")
      }
      //}

      // compute hot edges / node pairs
      val edgefreq = (trace zip trace.drop(1)) collectBy(x=>x, _.length);
      println("hot edges:")
      val hotedges = edgefreq.toSeq.sortBy(-_._2)
      hotedges.take(10).foreach(println)
      println()

      //if (verbose) {
      if (!hotedges.isEmpty) {
        val hottestEdge = hotedges.head
        println("hottest")
        println(hottestEdge)
        println()
      } else {
        println("NO hot edges")
      }
      //}
      
      // calc pred and succ
      val pred = (trace zip trace.drop(1)) collectBy(_._2, _.map(_._1).distinct);
      val succ = (trace zip trace.drop(1)) collectBy(_._1, _.map(_._2).distinct);


      /* main analysis part follows:

         Find the `pivot` node: the most frequent one which is not already a self-loop.
         Identify all traces from pivot to pivot.
         This set of traces corresponds to a trace tree (Franz/Gal), but we don't stop here.
         Collapse each trace into a single block:
              ... A B A C D A B A E F A B A C D A B A ...
                        becomes with pivot A:
              ... A [BA] [CDA] [BA] [EFA] [BA] [CDA] [BA] ...
         We continue the process. [BA] will be the new pivot, and we group:
              ... A [BA] [[CDA][BA]] [[EFA][BA]] [[CDA][BA]] ...
         Next iteration will group:
              ... A [BA] [CDABAEFABA] [CDABAEFABA] ...
         And now we stop, having reached a self-loop.
      */

      def isLoop(a: Int) = succ.getOrElse(a,Seq()) contains a
      val hotspotsNoLoop = hotspots.map(_._1).filterNot(isLoop)
      val pivot = hotspotsNoLoop.takeWhile(a=>freq(a) == freq(hotspotsNoLoop.head)).last

      if (freq(pivot) == 1) { // done, only loops remain
        gg.printGraph("%03d_A".format(step))(mergeHist,maxloopcount,freq,edgefreq,Map.empty)(Nil)
        return trace
      }

      gg.printGraph("%03d_A".format(step))(mergeHist,maxloopcount,freq,edgefreq,Map.empty)(List((pivot,pivot)))

      val ignoreHeadAndTail = true

      val traces0 = splitWhere(trace)(_ == pivot)
      val traces = if (ignoreHeadAndTail)
          traces0.head.map(List(_)) ++ traces0.tail.init ++ traces0.last.map(List(_))
        else
          traces0
      val hottraces = traces.groupBy(x=>x).map{case(k,v)=>(k,v.length)}.toSeq.sortBy(-_._2)

      println
      println("5 hot traces")
      //hottraces.take(5).foreach{case(t,c)=>println("---"+c);t.foreach(println)}
      hottraces.take(10).foreach(p=>println(p._2+"*"+p._1.mkString(" ")))

      // build a trace of traces ...

      println("block <-> index:")
      val indexToBlock2 = traces.distinct.toArray
      val blockToIndex2 = indexToBlock2.zipWithIndex.toMap
      println(blockToIndex2)

      trace = (traces map blockToIndex2).toVector

      println
      println("trace")
      println(trace)

      analyze(step+1)

    }

    try {
      analyze(0)
    } finally {
      gg.finish()
    }
  }

}

/* ---------- PART 4: high-level term interpreter ---------- */

trait ProgEval extends LangX {
  type Term1 = Rep[Term]

  def arr[A](x: Arr[A]): Term1 = record("tag"->lift("arr"),"val"->x.asInstanceOf[Rep[Any]])
  implicit def num(x: Rep[Int]): Term1 = record("tag"->lift("num"),"val"->x)
  implicit def num(x: Int): Term1 = num(lift(x))
  implicit def sym(s: String): Term1 = record("tag"->lift("sym"),"val"->lift(s))

  def nil = record("tag"->lift("nil"))
  def cons(x: Term1, y: Term1): Term1 = record("tag"->lift("pair"),"car"->x,"cdr"->y)
  def car(x: Term1): Term1 = field(x,"car")
  def cdr(x: Term1): Term1 = field(x,"cdr")

  def toArr[A](x: Term1): Arr[A] = field(x,"val").asInstanceOf[Arr[A]]
  def toInt(x: Term1): Rep[Int] = field(x,"val").asInstanceOf[Rep[Int]]
  def toStr(x: Term1): Rep[String] = x/*field(x,"val")*/.asInstanceOf[Rep[String]]

  def tagOf(x: Term1): Rep[String] = field(x,"tag").asInstanceOf[Rep[String]]

  def ife(c: Term1, a: =>Term1, b: => Term1): Term1 = if (int_equ(toInt(c),lift(0))) b else a
  def plus(x: Term1, y: Term1): Term1 = num(toInt(x) + toInt(y))
  def minus(x: Term1, y: Term1): Term1 = num(toInt(x) - toInt(y))
  def times(x: Term1, y: Term1): Term1 = num(toInt(x) * toInt(y))
  def equs(x: Term1, y: Term1): Term1 = if (str_equ(tagOf(x),tagOf(y))) { if (str_equ(toStr(x),toStr(y))) num(1) else num(0) } else num(0)
  def equi(x: Term1, y: Term1): Term1 = if (int_equ(toInt(x),toInt(y))) num(1) else num(0)
  def ltei(x: Term1, y: Term1): Term1 = if (int_lte(toInt(x),toInt(y))) num(1) else num(0)

  def isNumber(x: Term1): Term1 = if (str_equ(tagOf(x), lift("num"))) num(1) else num(0)
  def isSymbol(x: Term1): Term1 = if (str_equ(tagOf(x), lift("sym"))) num(1) else num(0)

  def lookup: Fun2[Term,Term,Term] = fun2("lookup") { (x,env) =>
    //println("LOOKUP:"+x+":"+env)
    ife(equs(x, car(car(env))), cdr(car(env)),
        lookup(x,cdr(env)))
  }

  def my_arr_new: Term1 = {newMyArr[Term]; num(0)}
  def my_arr: Term1 = arr(myArr[Term])
  def arr_get(a: Term1, i: Term1): Term1 = {
    //println("ARR_GET:"+a)
    arr_apply(toArr(a), toInt(i))
  }
  def arr_put(a: Term1, i: Term1, v: Term1): Term1 = {
    //println("ARR_PUT:"+a+":"+i+":"+v)
    arr_update(toArr(a), toInt(i), v); num(0)
  }
  def eprint(n: Int, x: Term1): Term1 = { /*iprint(n,x);*/ num(0) }

  def eval: Fun2[Term,Term,Term] = fun2("eval") { (e,env) =>
    begin(eprint(1,e),
    ife(isNumber(e),                  e,
    ife(isSymbol(e),                  lookup(e,env),
    ife(equs(sym("lambda"), car(e)),  cons(e,env),
    ife(equs(sym("ife"), car(e)),     ife(eval(car(cdr(e)),env), eval(car(cdr(cdr(e))),env), eval(car(cdr(cdr(cdr(e)))),env)),
    ife(equs(sym("sym"), car(e)),     car(cdr(e)),
    ife(equs(sym("quote"), car(e)),   car(cdr(e)),
    ife(equs(sym("isNumber"), car(e)),isNumber(eval(car(cdr(e)),env)),
    ife(equs(sym("isSymbol"), car(e)),isSymbol(eval(car(cdr(e)),env)),
    ife(equs(sym("equs"), car(e)),    equs(eval(car(cdr(e)),env), eval(car(cdr(cdr(e))),env)),
    ife(equs(sym("equi"), car(e)),    equi(eval(car(cdr(e)),env), eval(car(cdr(cdr(e))),env)),
    ife(equs(sym("ltei"), car(e)),    ltei(eval(car(cdr(e)),env), eval(car(cdr(cdr(e))),env)),
    ife(equs(sym("plus"), car(e)),    plus(eval(car(cdr(e)),env), eval(car(cdr(cdr(e))),env)),
    ife(equs(sym("minus"), car(e)),   minus(eval(car(cdr(e)),env), eval(car(cdr(cdr(e))),env)),
    ife(equs(sym("times"), car(e)),   times(eval(car(cdr(e)),env), eval(car(cdr(cdr(e))),env)),
    ife(equs(sym("cons"), car(e)),    cons(eval(car(cdr(e)), env), eval(car(cdr(cdr(e))),env)),
    ife(equs(sym("car"), car(e)),     car(eval(car(cdr(e)),env)),
    ife(equs(sym("cdr"), car(e)),     cdr(eval(car(cdr(e)),env)),
    ife(equs(sym("my_arr_new"), car(e)), my_arr_new,
    ife(equs(sym("my_arr"), car(e)),     my_arr,
    ife(equs(sym("arr_get"), car(e)),    arr_get(eval(car(cdr(e)),env), eval(car(cdr(cdr(e))), env)),
    ife(equs(sym("arr_put"), car(e)),    arr_put(eval(car(cdr(e)),env), eval(car(cdr(cdr(e))), env), eval(car(cdr(cdr(cdr(e)))), env)),
    ife(equs(sym("eprint"), car(e)),     eprint(1,eval(car(cdr(e)),env)),
    {
      //println("EXP: "+e)
      //println("CAR(e): "+car(e))
      //println("CAR(CDR(e)): "+car(cdr((e))))
                                         apply(eval(car(e),env), eval(car(cdr(e)),env))  // eval only one arg?
    }
    )))))))))))))))))))))))
  }

  def apply: Fun2[Term,Term,Term] = fun2("apply") { (f,x) => // ((lambda f x body) env) @ x
    //println(s"apply $f @ $x")
    begin(eprint(1,car(cdr(car(f)))),
    eval(car(cdr(cdr(cdr(car(f))))), cons(cons(car(cdr(cdr(car(f)))), x), cons(cons(car(cdr(car(f))), f), cdr(f)))))
  }

  def list(xs: Term1*): Term1 = if (xs.isEmpty) nil else cons(xs.head, list(xs.tail:_*))

  // DONE #1: run in low-level interpreter
  //   - 1 level of interpretation
  //
  // DONE #2: meta-interpreter
  //   - 2 levels of interpretation

  def data(x: Any): Term1 = x match {
    case u: Unit => num(0)
    case b: Boolean => if (b) num(1) else num(0)
    case n: Int => num(n)
    case s: String => sym(s)
    case Nil => nil
    case x::xs => cons(data(x), data(xs))
  }

  def global_env(order: List[String], funs: Map[String, Any], deps: Map[String,List[String]], env: Term1 = nil): Term1 = order match {
    case Nil => env
    case x::xs =>
      var f = funs(x)
      deps.get(x) match {
        case None =>
        case Some(ds) =>
          def let(name: String, e1: Any, e2: Any): Any =
            List(List("lambda", "_", name, e2), e1)
          def wrap1(d: String, b: Any): Any = {
            let(d, funs(d), b)
          }
          val List("lambda", fn, fa, fr) = f
          var b = fr
          for (d <- ds) {
            b = wrap1(d, b)
          }
          f = List("lambda", fn, fa, b)
      }
      global_env(xs, funs, deps, cons(cons(x, cons(data(f), env)), env))
  }
}


trait RunHighLevel extends ProgEval with LangLowLevel {
  def runProg(code: =>Term1, env: =>Term1) = {
    //println(eval(id,nil))

    prog.clear
    label = "main"

    val ev = eval

    stms = stms :+ Put(Mem,Const("in"),code) :+ Put(Mem,Const("env"),env)

    val res = ev(Get(Mem,Const("in")),Get(Mem,Const("env")))
    stms = stms :+ Output(res)
    prog(label) = Block(stms, Done)

    trace = Vector.empty
    mem.clear

    //mem("in") = prog1
    mem("sd") = 0
    mem("sp") = mutable.Map(0 -> mutable.Map())

    //mem("hd") = 0
    //mem("hp") = mutable.Map()

    //println(prog)

    exec("main")

  }
}

/* ---------- PART 5: translate code into data for interpreter ---------- */

trait Code2Data extends Lang {
  type Rep[+T] = Any
  type Fun[A,B] = String
  type Arr[A] = Any
  private var _order: List[String] = Nil
  private val _funs = mutable.Map[String,Any]()
  private val _deps = mutable.Map[String,mutable.LinkedHashSet[String]]()
  var counter = 0
  def fresh_var[A]: String = {
    counter += 1
    "x"+counter
  }
  def begin_macro(x: Any, xs: Any*): Any = xs match {
    case Nil => x
    case _ => List(List("lambda", "_", "_", begin_macro(xs.head, xs.tail:_*)), x)
  }
  override def begin[T](a: => Any, b: => Rep[T]): Rep[T] = begin_macro(a, b)
  override def begin[T](a: => Any, b: => Any, c: => Rep[T]): Rep[T] = begin_macro(a, b, c)
  override def begin[T](a: => Any, b: => Any, c: => Any, d: => Rep[T]): Rep[T] = begin_macro(a, b, c, d)
  override def begin[T](a: => Any, b: => Any, c: => Any, d: => Any, e: => Rep[T]): Rep[T] = begin_macro(a, b, c, d, e)
  override def newMyArr[A]: Rep[Unit] = List("my_arr_new")
  override def myArr[A]: Arr[A] = List("my_arr")
  override def arr_apply[A](a: Arr[A], i: Rep[Int]): Rep[A] = List("arr_get", a, i)
  override def arr_update[A](a: Arr[A], i: Rep[Int], v: Rep[A]): Rep[Any] = List("arr_put", a, i, v)
  override def fun[A,B](name: String)(f: Rep[A]=>Rep[B]): Fun[A,B] = {
    val arg = fresh_var[A]
    _funs.get(name) match {
      case None =>
        _order = name::_order
        _funs(name) = "TODO"
        val r = f(arg)
        _funs(name) = List("lambda", name, arg, r)
      case Some("TODO") =>
        val ds = _order.takeWhile(_ != name)
        for (d <- ds; if _funs(d)=="TODO") {
          _deps.get(name) match {
            case None =>
              _deps(name) = new mutable.LinkedHashSet()
              _deps(name) += d
            case Some(_) =>
              _deps(name) += d
          }
        }
      case Some(_) =>
    }
    name
  }
  override def fun_apply[A,B](f:Fun[A,B],x:Rep[A]):Rep[B] = List(f, x)
  implicit override def lift[T](x: T): Rep[T] = x
  override def int_equ(x:Rep[Int],y:Rep[Int]):Rep[Boolean] = List("equi", x, y)
  override def int_lte(x:Rep[Int],y:Rep[Int]):Rep[Boolean] = List("ltei", x, y)
  override def int_plus(x:Rep[Int],y:Rep[Int]):Rep[Int] = List("plus", x, y)
  override def int_minus(x:Rep[Int],y:Rep[Int]):Rep[Int] = List("minus", x, y)
  override def int_times(x:Rep[Int],y:Rep[Int]):Rep[Int] = List("times", x, y)

  override def __ifThenElse[T](c: Rep[Boolean], a: => Rep[T], b: => Rep[T]): Rep[T] = List("ife", c, a, b)

  override def str_equ(x:Rep[String],y:Rep[String]):Rep[Boolean] = List("equs", x, y)

  override def pair(x: Rep[Any], y: Rep[Any]): Rep[Any] = List("cons", x, y)
  override def fst[A](t: Rep[Any]): Rep[A] = List("car", t)
  override def snd[A](t: Rep[Any]): Rep[A] = List("cdr", t)

  def funs: Map[String,Any] = _funs.toMap
  def order: List[String] = _order filter {name =>
    val ds = _order dropWhile (_ != name)
    (for (d <- ds;
          s <- deps.get(d);
          if s contains name) yield d).isEmpty
  }
  def deps: Map[String,List[String]] = (for ((k,v) <- _deps) yield (k,v.toList)).toMap
}

trait Code2DataProgEval extends ProgEval with Code2Data {
  // LangX stubs
  def iprint(n: Int, x: Rep[Any]): Rep[Unit] = ???
  def record(xs: (String,Rep[Any])*): Rep[Term] = ???
  def field(x: Rep[Term], k: String): Rep[Term] = ???
  def newArr[A](name: String): Rep[Unit] = ???
  def getArr[A](name: String): Arr[A] = ???

  type Fun2[A,B,C] = Fun[(A,B),C]
  def fun2[A,B,C](name: String)(f: (Rep[A],Rep[B])=>Rep[C]): Fun2[A,B,C] = fun(name) { t: Rep[(A,B)] =>
    f(car(t), cdr(t))
  }
  def fun2_apply[A,B,C](f:Fun2[A,B,C], a:Rep[A], b:Rep[B]): Rep[C] = fun_apply(f, cons(a,b))

  override def sym(s: String): Term1 = List("sym", s)

  override def cons(x: Term1, y: Term1): Term1 = List("cons", x, y)
  override def car(x: Term1): Term1 = List("car", x)
  override def cdr(x: Term1): Term1 = List("cdr", x)

  override def ife(c: Term1, a: =>Term1, b: => Term1): Term1 = List("ife", c, a, b)
  override def plus(x: Term1, y: Term1): Term1 = List("plus", x, y)
  override def minus(x: Term1, y: Term1): Term1 = List("minus", x, y)
  override def times(x: Term1, y: Term1): Term1 = List("times", x, y)
  override def equs(x: Term1, y: Term1): Term1 = List("equs", x, y)
  override def equi(x: Term1, y: Term1): Term1 = List("equi", x, y)
  override def ltei(x: Term1, y: Term1): Term1 = List("ltei", x, y)

  override def isNumber(x: Term1): Term1 = List("isNumber", x)
  override def isSymbol(x: Term1): Term1 = List("isSymbol", x)

  override def my_arr_new: Term1 = List("my_arr_new")
  override def my_arr: Term1 = List("my_arr")
  override def arr_get(a: Term1, i: Term1): Term1 = List("arr_get", a, i)
  override def arr_put(a: Term1, i: Term1, v: Term1): Term1 = List("arr_put", a, i, v)
  override def eprint(n: Int, x: Term1): Term1 = List("eprint", x) // FIXME: ident
}

/* ---------- PART 6: tests ---------- */

trait Program[A,B] {
  def id: String
  def program(c: Lang): c.P[A,B]
}
import org.scalatest.FunSuite
trait ProgramFunSuite[A,B] extends FunSuite with Program[A,B] {
  def analyze: Boolean
  test(id+": direct execution") {
    val c = new LangDirect {}
    val p = program(c)
    import c._
    assert(p.f(p.a) === p.b)
  }

  test(id+": translate to low-level code and interpret") {
    val c = new RunLowLevel with Analyze {
      override def report(name: String) = {
        //println(prog)
        trace.foreach(println)

        println("hotspots:")
        val hotspots = trace.groupBy(x=>x).map{ case (k,v)=>(k,v.length) }.toSeq.sortBy(-_._2)
        hotspots.take(10).foreach(println)
        println()

        super.report(name)
      }
    }
    val p = program(c)
    import c._
    runLow(p.f, ev(p.a))
    assert(out === ev(p.b))
    if (analyze) report(id+"-low")
  }

  test(id+": execute in high-level interpreter, which is executed directly") {
    val d = new Code2Data {}
    val p = program(d)
    val fn = p.f
    val i = new ProgEval with LangDirect
    import i._
    assert(eval(list(fn, data(p.a)), global_env(d.order, d.funs, d.deps)) === data(p.b))
  }

  test(id+": execute in high-level interpreter, which is mapped to low-level code, which is interpreted") {
    val d = new Code2Data {}
    val p = program(d)
    val fn = p.f
    val i = new ProgEval with LangLowLevel with RunHighLevel with Analyze
    import i._
    runProg(list(sym(fn), data(p.a)), global_env(d.order, d.funs, d.deps))
    assert(out === ev(data(p.b)))
    if (analyze) report(id+"-high")
  }

  test(id+": double-interpretation, direct") {
    val di = new Code2DataProgEval {}
    val en = di.eval

    val d = new Code2Data {}
    val p = program(d)
    val fn = p.f

    val i = new ProgEval with LangDirect
    import i._
    assert(eval(list(en, list("cons", list("quote", list(fn, data(p.a))), list("quote", global_env(d.order, d.funs, d.deps)))), global_env(di.order, di.funs, di.deps)) === data(p.b))
  }

  test(id+": double-interpretation, low-level") {
    val di = new Code2DataProgEval {}
    val en = di.eval

    val d = new Code2Data {}
    val p = program(d)
    val fn = p.f

    val i = new ProgEval with LangLowLevel with RunHighLevel with Analyze
    import i._
    runProg(list(sym(en), list(sym("cons"), list(sym("quote"), list(sym(fn), data(p.a))), list(sym("quote"), global_env(d.order, d.funs, d.deps)))), global_env(di.order, di.funs, di.deps))
    assert(out === ev(data(p.b)))
    if (analyze) report(id+"-high2")
  }
}

trait ProgramFactorial extends Program[Int,Int] {
  override def id = "factorial"
  def program(c: Lang): c.P[Int,Int] = {
    import c._
    def fac: Fun[Int,Int] = fun("fac") { n: Rep[Int] =>
      if (n === 0) {
        1
      } else {
        n * fac(n - 1)
      }
    }
    new P[Int,Int] {
      def f = fac
      def a = 10//4
      def b = 3628800//24
    }
  }
}

trait ProgramFactorialNoisy extends Program[Any,Int] {
  override def id = "factorial-noisy"
  def program(c: Lang): c.P[Any,Int] = {
    import c._
    def fac: Fun[Any,Int] = fun("fac") { a: Rep[Any] =>
      def a1 = fst[Int](a)
      def a2 = snd[Int](a)
      def n = a1 + a2
      if (n === 0) {
        1
      } else {
        n * fac(if (a1===0) pair(a1, a2-1) else pair(a1-1, a2))
      }
    }
    new P[Any,Int] {
      def f = fac
      def a = pair(2,2)
      def b = 24
    }
  }
}

trait ProgramPascal extends Program[Any,Int] {
  override def id = "pascal"
  def program(c: Lang): c.P[Any,Int] = {
    import c._
    def pascal: Fun[Any,Int] = fun("pascal") { a: Rep[Any] =>
      def c = fst[Int](a)
      def r = snd[Int](a)
      if (c <= 0 || r <= c) 1
      else pascal(pair(c - 1, r - 1)) + pascal(pair(c, r - 1))
    }
    new P[Any,Int] {
      def f = pascal
      def a = pair(3,6)
      def b = 20
    }
  }
}

trait ProgramNested extends Program[Int,Int] {
  override def id = "nested"
  def program(c: Lang): c.P[Int,Int] = {
    import c._
    def inner: Fun[Int,Int] = fun("inner") { i: Rep[Int] =>
      if (i === 0) 1
      else i+inner(i-1)
    }
    def nested: Fun[Int,Int] = fun("nested") { n: Rep[Int] =>
      if (n === 0) 1
      else inner(n)+nested(n-1)
    }
    new P[Int,Int] {
      def f = nested
      def a = 4
      def b = 25
    }
  }
}

trait ProgramFib extends Program[Int,Int] {
  override def id = "fib"
  def program(c: Lang): c.P[Int,Int] = {
    import c._
    def fib: Fun[Int,Int] = fun("fib") { n: Rep[Int] =>
      if (n <= 1) n
      else fib(n-1)+fib(n-2)
    }
    new P[Int,Int] {
      def f = fib
      def a = 12
      def b = 144
    }
  }
}

trait ProgramSieve extends Program[Int,Int] { z =>
  override def id = "sieve"
  def a: Int
  def b: Int
  def program(c: Lang): c.P[Int,Int] = {
    import c._
    val id_n = 0
    val id_i = 1
    def primes = myArr[Int]
    def n = primes(id_n)
    def i = primes(id_i)
    def init: Fun[Int,Unit] = fun("init") {i: Rep[Int] =>
      begin(
        (primes(i) = 1),
        (if (i === n) unit else init(i+1)))
    }
    def mark: Fun[Int,Unit] = fun("mark") {k: Rep[Int] =>
      if ((n+1) <= k) unit
      else begin(
        (primes(k) = 0),
        (mark(k+i)))
    }
    def algo: Fun[Int,Unit] = fun("algo") {i: Rep[Int] =>
      begin(
        (primes(id_i) = i),
        (if (primes(i) === 0) unit else mark(i+i)),
        (if (i === n) unit else algo(i+1)))
    }
    def sieve: Fun[Int,Int] = fun("sieve") { x: Rep[Int] =>
      begin(
        (newMyArr[Int]),
        (primes(id_n) = x),
        (init(2)),
        (algo(2)),
        (primes(x)))
    }
    new P[Int,Int] {
      def f = sieve
      def a = z.a
      def b = z.b
    }
  }
}

trait ProgramEven extends Program[Int,Int] { z =>
  override def id = "even"
  def a: Int
  def b: Int
  def program(c: Lang): c.P[Int,Int] = {
    import c._
    def even: Fun[Int,Int] = fun("even") {i: Rep[Int] =>
      if (i === 0) 1
      else odd(i-1)
    }
    def odd: Fun[Int,Int] = fun("odd") {i: Rep[Int] =>
      if (i === 0) 0
      else even(i-1)
    }
    new P[Int,Int] {
      def f = even
      def a = z.a
      def b = z.b
    }
  }
}

abstract class ProgramFactorialFunSuite extends ProgramFunSuite[Int,Int] with ProgramFactorial
class TestProgramFactorial extends ProgramFactorialFunSuite {
  override def analyze = false
}
class AnalyzeProgramFactorial extends ProgramFactorialFunSuite {
  override def analyze = true
}
abstract class ProgramFactorialNoisyFunSuite extends ProgramFunSuite[Any,Int] with ProgramFactorialNoisy
class TestProgramFactorialNoisy extends ProgramFactorialNoisyFunSuite {
  override def analyze = false
}
class AnalyzeProgramFactorialNoisy extends ProgramFactorialNoisyFunSuite {
  override def analyze = true
}
abstract class ProgramPascalFunSuite extends ProgramFunSuite[Any,Int] with ProgramPascal
class TestProgramPascal extends ProgramPascalFunSuite {
  override def analyze = false
}
class AnalyzeProgramPascal extends ProgramPascalFunSuite {
  override def analyze = true
}
abstract class ProgramNestedFunSuite extends ProgramFunSuite[Int,Int] with ProgramNested
class TestProgramNested extends ProgramNestedFunSuite {
  override def analyze = false
}
class AnalyzeProgramNested extends ProgramNestedFunSuite {
  override def analyze = true
}
abstract class ProgramFibFunSuite extends ProgramFunSuite[Int,Int] with ProgramFib
class TestProgramFib extends ProgramFibFunSuite {
  override def analyze = false
}
class AnalyzeProgramFib extends ProgramFibFunSuite {
  override def analyze = true
}
abstract class ProgramSieveFunSuite extends ProgramFunSuite[Int,Int] with ProgramSieve
abstract class ProgramSievePosFunSuite extends ProgramSieveFunSuite {
  override def id = super.id+"-pos"
  override def a = 7
  override def b = 1
}
abstract class ProgramSieveNegFunSuite extends ProgramSieveFunSuite {
  override def id = super.id+"-neg"
  override def a = 4
  override def b = 0
}
class TestProgramSievePos extends ProgramSievePosFunSuite {
  override def analyze = false
}
class AnalyzeProgramSievePos extends ProgramSievePosFunSuite {
  override def analyze = true
}
class TestProgramSieveNeg extends ProgramSieveNegFunSuite {
  override def analyze = false
}
class AnalyzeProgramSieveNeg extends ProgramSieveNegFunSuite {
  override def analyze = true
}
abstract class ProgramEvenFunSuite extends ProgramFunSuite[Int,Int] with ProgramEven
abstract class ProgramEvenPosFunSuite extends ProgramEvenFunSuite {
  override def id = super.id+"-pos"
  override def a = 4
  override def b = 1
}
abstract class ProgramEvenNegFunSuite extends ProgramEvenFunSuite {
  override def id = super.id+"-neg"
  override def a = 7
  override def b = 0
}
class TestProgramEvenPos extends ProgramEvenPosFunSuite {
  override def analyze = false
}
class AnalyzeProgramEvenPos extends ProgramEvenPosFunSuite {
  override def analyze = true
}
class TestProgramEvenNeg extends ProgramEvenNegFunSuite {
  override def analyze = false
}
class AnalyzeProgramEvenNeg extends ProgramEvenNegFunSuite {
  override def analyze = true
}
