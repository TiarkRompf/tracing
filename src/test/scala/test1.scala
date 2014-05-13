package test1

import scala.language.implicitConversions

import java.io._
import scala.collection._



object Test {

  type Label = String
  type Obj = mutable.Map[Any,Any]

  case class Block(stms: List[Stm], cont: Jump) {
    override def toString = {
      "{\n" + stms.map(_ +"\n").mkString("")+cont + "\n}"
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

  abstract class Exp
  case class Const(x: Any) extends Exp {
    override def toString = {
      s"Const(${x.toString.take(10)})"
    }
  }
  case class Plus(x: Exp, y: Exp) extends Exp
  case class Minus(x: Exp, y: Exp) extends Exp
  case class Times(x: Exp, y: Exp) extends Exp
  case class Equal(x: Exp, y: Exp) extends Exp
  case class ITE(c: Exp, x: Exp, y: Exp) extends Exp
  case class Get(a: Exp, b: Exp) extends Exp  // a[b]
  case object Mem extends Exp

  val prog = mutable.Map[Label,Block](
    "a" -> Block(Print(Const("hello"))::Nil, Done)
  )


  var trace: Vector[String] = Vector.empty
  val mem: Obj = mutable.Map()

  def ev(e: Exp): Any = e match {
    case Mem => mem
    case Const(c) => c
    case Get(a,b) => (eval[Obj](a))(ev(b))
    case Equal(a,b) => ev(a) == ev(b)
    case ITE(c,a,b) => if (eval[Boolean](c)) ev(a) else ev(b)
    case Plus(a,b) => eval[Int](a) + eval[Int](b)
    case Minus(a,b) => eval[Int](a) - eval[Int](b)
    case Times(a,b) => eval[Int](a) * eval[Int](b)
  }

  def eval[T](e: Exp): T = ev(e).asInstanceOf[T]

  def exec(name: Label): Unit = {
    trace = trace :+ name
    exec(prog(name))
  }
  def exec(block: Block): Unit = { block.stms.foreach(exec); exec(block.cont) }
  def exec(jump: Jump): Unit = jump match {
    case Done => 
    case Goto(l) => 
      exec(eval[Label](l))
    case IfElse(c,a,b) => if (eval[Boolean](c)) exec(a) else exec(b)
    case Guard(l,x,b) => 
      val x1 = eval[Label](l)
      if (x1 == x) exec(b)
      else exec(x1)
  }
  def exec(stm: Stm): Unit = { /*println(stm);*/ stm } match {
    case Print(a) => println(eval[Any](a))
    case Put(a,b,c) => (eval[Obj](a))(eval[Any](b)) = eval[Any](c)
    case New(a,b) => (eval[Obj](a))(eval[Any](b)) = new mutable.HashMap
  }


  def merge(l1: Label, l2: Label) = {

    val b2 = prog(l2)

    def merge0(b1: Block): Block = Block(b1.stms, merge1(b1.cont))
    def merge1(b1: Jump): Jump = b1 match {
      case Goto(t1) => Guard(t1,l2,b2)
      case Guard(tx,lx,bx) => Guard(tx,lx,merge0(bx))
    }

    val b1 = prog(l1)
    prog(l1) = merge0(b1)

  }

  def mergeAll(ls: List[Label]) = 
    if (ls.nonEmpty) for (l2 <- ls.tail) merge(ls.head,l2)


  def test1 = {
    case class Val[T](x:T)

    case class Fun[A,B](f: Val[A]=>Val[B]) {
      def apply(x:Val[A]) = f(x)
    }

    def fun[A,B](name: String)(f: Val[A]=>Val[B]): Fun[A,B] = Fun(f)

    def if_[A](c: Val[Boolean])(a: => Val[A])(b: => Val[A]): Val[A] = if (c.x) a else b

    implicit def lift[T](x: T) = Val(x)

    implicit class IntOps(x: Val[Int]) {
      def ===(y: Val[Int]) = Val(x.x == y.x)
      def +(y: Val[Int]) = Val(x.x + y.x)
      def -(y: Val[Int]) = Val(x.x - y.x)
      def *(y: Val[Int]) = Val(x.x * y.x)
    }

    def fac: Fun[Int,Int] = fun("fac") { n: Val[Int] =>
      if_(n === 0) {
        1
      } {
        n * fac(n - 1)
      }

    }

    println(fac(4))
  }


  def test2: Unit = {

    var label = "main"
    var stms: List[Stm] = Nil

    type Val[T] = Exp

    implicit def lift(x: Int): Exp = Const(x)
    implicit def lifts(x: String): Exp = Const(x)

    case class Fun[A,B](name: String, f: Val[A]=>Val[B]) {
      def apply(x:Val[A]) = {
        val uname = label+"-"+name
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
        prog(label) = Block(stms, Goto(name))

        label = ucont
        stms = Nil
        stms = stms :+ Put(Mem, "sd",Minus(sd,1))
        stms = stms :+ Put(fp, ures,Get(fp1,"res"))
        stms = stms :+ Put(sp,sd1,"null")
        Get(fp,ures)
      }
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

    def if_[A](c: Val[Boolean])(a: => Val[A])(b: => Val[A]): Val[A] = {

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


    implicit class IntOps(x: Val[Int]) {
      def ===(y: Val[Int]) = Equal(x,y)
      def +(y: Val[Int]) = Plus(x,y)
      def -(y: Val[Int]) = Minus(x,y)
      def *(y: Val[Int]) = Times(x,y)
    }

    def fac: Fun[Int,Int] = fun("fac") { n: Val[Int] =>
      if_(n === 0) {
        1
      } {
        n * fac(n - 1)
      }
    }

    prog.clear

    val res = fac(Get(Mem,Const("in")))
    stms = stms :+ Print(res)
    prog(label) = Block(stms, Done)

    def run() = {
      trace = Vector.empty
      mem.clear
      mem("in") = 6
      mem("sd") = 0
      mem("sp") = mutable.Map(0 -> mutable.Map())

      //println(prog)

      //println("---")

      exec("main")

      //println("---")

      //mem foreach println
    }

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
    println(splitWhere(List(1,2,3,4,5,6,7,8,9))(_ % 4 == 0))


    def runImprove() = {
      run()

      val hotspots = trace.groupBy(x=>x).map{ case (k,v)=>(k,v.length) }.toSeq.sortBy(-_._2)

      println("10 hotspots")
      hotspots.take(10).foreach(p=>println(p._2+"*"+p._1))

      val tracelets = splitWhere(trace)(_ == hotspots.head._1)

      val hottracelets = tracelets.groupBy(x=>x).map{case(k,v)=>(k,v.length)}.toSeq.sortBy(-_._2)

      println
      println("5 hot traces")
      hottracelets.take(5).foreach(p=>println(p._2+"*"+p._1.mkString(" ")))

      val hottest = hottracelets.head._1.toList

      println
      println("merge: "+hottest)
      mergeAll(hottest)

      println
    }

    runImprove()
    runImprove()
    runImprove()
    runImprove()
    runImprove()

    prog.foreach(println)


    return

    val trace0 = trace

    val rawlog = trace

    val hotspots = rawlog.groupBy(x=>x).map{ case (k,v)=>(k,v.length) }.toSeq.sortBy(-_._2)

    println("10 hotspots")
    hotspots.take(10).foreach(p=>println(p._2+"*"+p._1))



    val traces = splitWhere(rawlog)(_ == hotspots.head._1)

    val hottraces = traces.groupBy(x=>x).map{case(k,v)=>(k,v.length)}.toSeq.sortBy(-_._2)

    println
    println("5 hot traces")
    //hottraces.take(5).foreach{case(t,c)=>println("---"+c);t.foreach(println)}
    hottraces.take(10).foreach(p=>println(p._2+"*"+p._1.mkString(" ")))


    println

    // trace multiple levels

    def trace1(ppoints0: Seq[Any], norm: Boolean = true) = new {
      val points = ppoints0
      val uniqueMap = points.distinct.toSeq.zipWithIndex.toMap
      val normPoints = if (!norm) points else points map uniqueMap // OOM for points=rawlog if norm=true

      val hotPoints = normPoints.groupBy(x=>x).map{ case (k,v)=>(k,v.length) }.toSeq.sortBy(-_._2)

      val traces = splitWhere(normPoints)(_ == hotPoints.head._1)
    }


    val traces2 = trace1(traces)
    val traces3 = trace1(traces2.traces)
    val traces4 = trace1(traces3.traces)
    val traces5 = trace1(traces4.traces)

    println(traces2.hotPoints)
    //ArrayBuffer((54,89889), (69,27995), (53,24612), (167,23311), (170,22505), (171,22411), (182,20959), (217,13401), (103,12887), (113,12886), (180,12881), (204,11039), (184,10400), (172,10400), (197,10200), (317,10120), (318,10120), (320,10000), (321,10000), (154,3146), (82,2131), (143,1614), (160,1505), (162,1105), (159,1103), (158,1003), (203,916), (252,800), (355,716), (142,703), (181,609), (199,608), (202,607), (201,607), (205,607), (164,600), (237,517), (185,504), (206,504), (183,504), (178,504), (179,503), (176,503), (351,500), (177,429), (207,429), (189,402), (192,402), (191,402), (194,402), (190,402), (195,402), (308,401), (157,400), (168,400), (146,400), (163,400), (229,307), (243,306), (362,305), (123,305), (125,303), (124,303), (129,303), (134,303), (128,303), (148,303), (149,303), (223,303), (127,303), (72,303), (126,303), (122,303), (175,301), (138,300), (153,300), (152,300), (156,300), (169,300), (193,300), (173,300), (244,300), (166,300), (161,300), (155,300), (336,300), (186,300), (200,300), (150,230), (151,229), (209,206), (135,203), (231,202), (140,201), (247,200), (174,200), (196,200), (253,200), (133,200), (233,200), (248,200), (165,200), (188,200), (187,200), (245,200), (345,200), (198,200), (255,200), (145,200), (346,200), (136,200), (232,200), (259,199), (376,111), (375,111), (374,111), (373,111), (316,110), (319,110), (315,110), (234,105), (225,105), (242,105), (216,103), (238,103), (307,103), (220,103), (224,103), (298,103), (236,103), (230,103), (213,103), (240,103), (226,103), (304,103), (300,103), (227,103), (215,103), (222,103), (366,102), (367,102), (306,102), (368,102), (378,102), (305,102), (364,102), (365,101), (52,101), (372,101), (228,101), (371,101), (311,101), (241,101), (370,101), (218,101), (235,101), (214,101), (239,101), (358,101), (369,101), (347,100), (333,100), (249,100), (352,100), (340,100), (257,100), (344,100), (353,100), (147,100), (132,100), (334,100), (137,100), (361,100), (356,100), (141,100), (256,100), (339,100), (343,100), (335,100), (350,100), (274,100), (377,100), (251,100), (330,100), (342,100), (310,100), (338,100), (250,100), (363,100), (258,100), (139,100), (273,100), (341,100), (332,100), (131,100), (254,100), (322,100), (337,100), (354,100), (309,100), (323,99), (313,93), (385,92), (384,92), (383,92), (387,90), (386,90), (210,90), (388,75), (389,74), (394,74), (395,74), (221,66), (357,63), (349,63), (360,63), (359,63), (24,59), (23,59), (396,37), (392,37), (393,37), (391,37), (390,37), (408,10), (407,10), (379,9), (380,9), (41,9), (409,9), (34,8), (208,8), (299,8), (312,7), (60,7), (381,7), (59,7), (382,7), (40,7), (42,6), (74,6), (70,6), (73,6), (71,6), (39,6), (75,6), (268,6), (437,6), (283,6), (38,4), (290,4), (277,4), (83,4), (37,3), (421,3), (219,3), (438,3), (441,3), (246,3), (287,3), (36,3), (276,2), (269,2), (288,2), (301,2), (436,2), (284,2), (289,2), (261,2), (443,2), (280,2), (293,2), (265,2), (292,2), (452,2), (270,2), (297,2), (275,2), (33,2), (92,2), (285,2), (266,2), (279,2), (444,2), (423,2), (286,2), (291,2), (281,2), (445,2), (144,2), (76,2), (303,2), (271,2), (108,2), (399,2), (278,2), (267,2), (35,2), (295,2), (282,2), (263,2), (31,2), (314,2), (26,2), (272,2), (262,2), (422,2), (294,2), (47,2), (442,2), (101,1), (0,1), (88,1), (115,1), (5,1), (449,1), (120,1), (440,1), (10,1), (56,1), (404,1), (417,1), (25,1), (14,1), (110,1), (460,1), (20,1), (46,1), (93,1), (416,1), (325,1), (448,1), (57,1), (78,1), (29,1), (211,1), (106,1), (121,1), (348,1), (84,1), (397,1), (61,1), (453,1), (89,1), (411,1), (116,1), (428,1), (1,1), (6,1), (117,1), (439,1), (85,1), (102,1), (302,1), (260,1), (28,1), (424,1), (429,1), (21,1), (65,1), (435,1), (97,1), (329,1), (461,1), (456,1), (324,1), (403,1), (9,1), (420,1), (109,1), (328,1), (77,1), (212,1), (96,1), (457,1), (13,1), (105,1), (2,1), (398,1), (412,1), (425,1), (430,1), (32,1), (264,1), (45,1), (64,1), (296,1), (17,1), (402,1), (22,1), (44,1), (118,1), (27,1), (413,1), (12,1), (49,1), (86,1), (406,1), (419,1), (81,1), (451,1), (7,1), (434,1), (98,1), (91,1), (66,1), (130,1), (455,1), (3,1), (431,1), (80,1), (426,1), (112,1), (458,1), (48,1), (63,1), (18,1), (414,1), (95,1), (327,1), (50,1), (67,1), (331,1), (16,1), (11,1), (446,1), (43,1), (450,1), (99,1), (87,1), (104,1), (55,1), (114,1), (401,1), (418,1), (8,1), (119,1), (58,1), (433,1), (447,1), (432,1), (410,1), (30,1), (51,1), (405,1), (19,1), (326,1), (107,1), (4,1), (79,1), (400,1), (94,1), (415,1), (427,1), (459,1), (15,1), (68,1), (62,1), (90,1), (111,1), (454,1), (100,1))

    println(traces3.hotPoints)
    //ArrayBuffer((29,20959), (136,10120), (36,10100), (141,10000), (140,10000), (139,10000), (15,1614), (40,916), (14,703), (28,609), (41,607), (42,504), (27,503), (26,429), (38,303), (18,303), (20,300), (32,300), (22,300), (67,300), (23,300), (30,300), (65,201), (10,200), (24,200), (33,200), (59,200), (39,200), (35,200), (31,200), (68,200), (79,198), (138,110), (137,110), (135,110), (44,106), (125,103), (170,102), (169,102), (124,102), (166,102), (56,101), (57,101), (164,101), (61,101), (60,101), (165,101), (64,101), (49,101), (66,101), (167,101), (48,101), (63,101), (50,101), (55,101), (51,101), (163,101), (62,101), (153,100), (37,100), (25,100), (157,100), (152,100), (78,100), (132,100), (74,100), (70,100), (21,100), (97,100), (77,100), (13,100), (129,100), (73,100), (128,100), (34,100), (148,100), (17,100), (149,100), (71,100), (12,100), (159,100), (76,100), (162,100), (123,100), (145,100), (150,100), (127,100), (11,100), (99,100), (158,100), (75,100), (151,100), (168,100), (146,100), (19,100), (126,100), (131,100), (142,99), (98,99), (72,99), (133,93), (174,92), (176,92), (175,92), (45,90), (182,74), (54,66), (53,65), (147,64), (160,63), (156,63), (161,63), (155,63), (177,54), (185,37), (179,37), (180,37), (181,37), (178,37), (184,36), (186,36), (183,36), (204,10), (203,10), (205,9), (171,9), (43,8), (173,7), (172,7), (130,7), (219,6), (107,6), (102,4), (103,4), (52,3), (69,2), (101,2), (234,2), (88,2), (115,2), (110,2), (93,2), (106,2), (121,2), (84,2), (89,2), (117,2), (85,2), (192,2), (92,2), (224,2), (109,2), (225,2), (96,2), (134,2), (105,2), (191,2), (118,2), (113,2), (108,2), (223,2), (112,2), (95,2), (16,2), (218,2), (114,2), (119,2), (82,2), (94,2), (90,2), (111,2), (122,2), (83,2), (0,1), (217,1), (5,1), (120,1), (202,1), (196,1), (189,1), (46,1), (228,1), (216,1), (211,1), (238,1), (221,1), (116,1), (1,1), (206,1), (233,1), (6,1), (201,1), (220,1), (229,1), (197,1), (9,1), (188,1), (193,1), (212,1), (237,1), (2,1), (144,1), (236,1), (86,1), (187,1), (81,1), (230,1), (7,1), (208,1), (213,1), (91,1), (198,1), (226,1), (3,1), (80,1), (209,1), (194,1), (199,1), (154,1), (143,1), (231,1), (87,1), (104,1), (8,1), (58,1), (235,1), (207,1), (214,1), (190,1), (210,1), (239,1), (4,1), (195,1), (47,1), (200,1), (227,1), (215,1), (222,1), (232,1), (100,1))

    println(traces4.hotPoints)
    //ArrayBuffer((17,10120), (19,10000), (18,110), (20,99), (10,98), (6,98), (15,92), (2,90), (26,56), (27,52), (33,35), (32,35), (39,10), (40,9), (1,8), (14,7), (24,6), (25,5), (23,4), (28,2), (0,1), (5,1), (42,1), (37,1), (29,1), (38,1), (21,1), (9,1), (13,1), (41,1), (34,1), (22,1), (12,1), (7,1), (3,1), (35,1), (16,1), (31,1), (11,1), (43,1), (8,1), (36,1), (30,1), (4,1))

    println(traces5.hotPoints)
    //ArrayBuffer((2,9900), (1,110), (3,99), (5,9), (0,1), (6,1), (4,1))


  }


  def main(args: Array[String]): Unit = {

    exec("a")

    test1
    test2
  }

/*

fac-ife-fac = {
  Put(Mem,Const(sd),Minus(Get(Mem,Const(sd)),Const(1)))
  Put(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(fac-ife-fa),Get(Get(Get(Mem,Const(sp)),Plus(Get(Mem,Const(sd)),Const(1))),Const(res)))
  Put(Get(Mem,Const(sp)),Plus(Get(Mem,Const(sd)),Const(1)),Const(null))
  Put(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(fac-if),Times(Get(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(arg)),Get(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(fac-ife-fa))))
  Guard(Const(fac-if),fac-if,{
    Put(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(res),Get(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(fac-if)))
    Goto(Get(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(ret)))
  })
}
fac-if = {
  Put(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(res),Get(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(fac-if)))
  Goto(Get(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(ret)))
}
main-fac = {
  Put(Mem,Const(sd),Minus(Get(Mem,Const(sd)),Const(1)))
  Put(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(main-fac),Get(Get(Get(Mem,Const(sp)),Plus(Get(Mem,Const(sd)),Const(1))),Const(res)))
  Put(Get(Mem,Const(sp)),Plus(Get(Mem,Const(sd)),Const(1)),Const(null))
  Print(Get(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(main-fac)))
  Done
}
main = {
  New(Get(Mem,Const(sp)),Plus(Get(Mem,Const(sd)),Const(1)))
  Put(Get(Get(Mem,Const(sp)),Plus(Get(Mem,Const(sd)),Const(1))),Const(arg),Get(Mem,Const(in)))
  Put(Get(Get(Mem,Const(sp)),Plus(Get(Mem,Const(sd)),Const(1))),Const(ret),Const(main-fac))
  Put(Mem,Const(sd),Plus(Get(Mem,Const(sd)),Const(1)))
  Goto(Const(fac))
}
fac = {
  IfElse(Equal(Get(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(arg)),Const(0)),Goto(Const(fac-ift)),Goto(Const(fac-ife)))
}
fac-ift = {
  Put(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(fac-if),Const(1))
  Goto(Const(fac-if))
}
fac-ife = {
  New(Get(Mem,Const(sp)),Plus(Get(Mem,Const(sd)),Const(1)))
  Put(Get(Get(Mem,Const(sp)),Plus(Get(Mem,Const(sd)),Const(1))),Const(arg),Minus(Get(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(arg)),Const(1)))
  Put(Get(Get(Mem,Const(sp)),Plus(Get(Mem,Const(sd)),Const(1))),Const(ret),Const(fac-ife-fa))
  Put(Mem,Const(sd),Plus(Get(Mem,Const(sd)),Const(1)))
  Guard(Const(fac),fac,{
    IfElse(Equal(Get(Get(Get(Mem,Const(sp)),Get(Mem,Const(sd))),Const(arg)),Const(0)),Goto(Const(fac-ift)),Goto(Const(fac-ife)))
  })
}

*/


}