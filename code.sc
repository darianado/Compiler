// A simple lexer inspired by work of Sulzmann & Lu
//==================================================
//
// call test with
//
//   amm code.sc small 
//   amm code.sc fib 
//   amm code.sc loops 
//   amm code.sc fact 
//   amm code.sc collatz
//


// regular expressions including records
abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp // records for extracting strings or tokens
case class RANGE(s: Set[Char]) extends Rexp 
case class PLUS(r: Rexp) extends Rexp 
case class OPTIONAL(r: Rexp) extends Rexp 
case class NTIMES(r: Rexp, n: Int) extends Rexp 

  
// values  
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
   
// some convenience for typing in regular expressions

def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RECD(_, r1) => nullable(r1)
  case RANGE(s) => false
  case PLUS(r1) => nullable(r1)
  case OPTIONAL(r1) => true
  case NTIMES(r1, i) => if (i == 0) true else nullable(r1)
}

def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)
  case RANGE(s) => if(s(c)) ONE else ZERO 
  case PLUS(r1) => SEQ(der(c,r1),STAR(r1))
  case OPTIONAL(r1) => der(c,r1)// + 0
  case NTIMES(r, i) =>if (i == 0) ZERO 
                      else SEQ(der(c, r), NTIMES(r, i - 1))
}


// extracts a string from a value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) ++ flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}


// extracts an environment from a value;
// used for tokenising a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}


// The injection and mkeps part of the lexer
//===========================================

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
  case PLUS(r) => Stars(Nil)
  case OPTIONAL(r) => Empty
  case NTIMES(r, i) => if(i==0) Empty 
                       else mkeps(r)
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  case (PLUS(r1), Sequ(v1, Stars(vs))) => Stars(inj(r1,c,v1)::vs)
  case (OPTIONAL(r),v) => inj(r,c,v)
  case (NTIMES(r,i), Sequ(v,vs)) => Sequ(inj(r,c,v),vs)
}


// lexing functions without simplification
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => inj(r, c, lex(der(c, r), cs))
}

def lexing(r: Rexp, s: String) = 
  env(lex(r, s.toList))



def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))

def F_ERROR(v: Val): Val = throw new Exception("error")

// simplification
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = 
  env(lex_simp(r, s.toList))


// The Lexing Rules for the WHILE Language

// def PLUS(r: Rexp) = r ~ r.%

def Range(s : List[Char]) : Rexp = s match {
  case Nil => ZERO
  case c::Nil => CHAR(c)
  case c::s => ALT(CHAR(c), Range(s))
}
def RANGE(s: String) = Range(s.toList)


val KEYWORD : Rexp = "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip"
val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | "<=" | ">=" | ":=" | "&&" | "||" 
val LETTER = RANGE("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
val SYMB = LETTER | RANGE(""".\_><=;,:""")
val WHITESPACE: Rexp  = PLUS(" " | "\n" | "\t" | "\r")
val DIGIT = RANGE("0123456789")
val STRING: Rexp = "\"" ~ (SYMB|WHITESPACE|DIGIT).% ~ "\""
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val RBRACE: Rexp = "}"
val LBRACE: Rexp = "{"
val SEMI: Rexp = ";"
val ID = LETTER ~ (RANGE("_") | LETTER | DIGIT).% 
val NUM = RANGE("0") | (RANGE("123456789") ~ DIGIT.%) 
val COMM : Rexp = ("""//""": Rexp) ~ (SYMB|(" ":Rexp)|DIGIT).% ~  ("\n": Rexp)


val WHILE_REGS = (("key" $ KEYWORD) |
                  ("comm" $ COMM) |
                  ("op" $ OP) |
                  ("id" $ ID) | 
                  // ("l" $ LETTER) |
                  ("sc" $ SEMI) |
                  ("symb" $ SYMB) |
                  ("w" $ WHITESPACE) |
                  ("d" $ DIGIT) |
                  ("str" $ STRING) |
                  ("p" $ (LPAREN | RPAREN | LBRACE | RBRACE)) |
                  ("nr" $ NUM)).%


// Simple While Tests
//========================

@arg(doc = "small tests")
@main
def small() = {
  println("-----test: a{3}")
  println(lex(NTIMES("a",3),"aaa".toList))
  //Sequ(Chr(a),Sequ(Chr(a),Sequ(Chr(a),Empty)))

  println("-----test: (a+one){3}")
  println(lex(NTIMES(ALT("a",ONE),3),"aa".toList))
  //Sequ(Left(Chr(a)),Sequ(Left(Chr(a)),Right(Empty)))

  val prog1 = """if"""
  println(s"-----test: $prog1")
  println(lexing(WHILE_REGS, prog1))

  val prog2 = """iffoo"""
  println(s"-----test: $prog2")
  println(lexing(WHILE_REGS, prog2))

  val prog3 = """read n;"""
  println(s"-----test: $prog3")
  println(lexing_simp(WHILE_REGS, prog3))
  //(key,read), (w, ), (id,n), (sc,;)

  val prog4 = """"read n;""""
  println(s"-----test: $prog4")
  println(lexing_simp(WHILE_REGS, prog4))
  //(str,"read n;")

  val prog5 = """read  n; write n"""  
  println(s"-----test: $prog5")
  println(lexing_simp(WHILE_REGS, prog5))
}


// Tests programs with filtering the white spaces
//==============

// escapes strings and prints them out as "", "\n" and so on
def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.collect{ 
    // case ("w",_) => None
    case (s1, s2) if s1!="w" => (s1, esc(s2))
    }

///////////////////////////////////////////////////////////////
val prog1 = """
write "Fib: ";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do {
temp := minus2;
minus2 := minus1 + minus2;
minus1 := temp;
n := n - 1
};
write "Result: ";
write minus2 ;
write "\n"
"""

@arg(doc = "Fibonacci test")
@main
def fib() = {
  println("lexing fib program")
  println(escape(lexing_simp(WHILE_REGS, prog1)).mkString("\n"))
}

// (key,"write")
// (str,"\"Fib: \"")
// (sc,";")
// (key,"read")
// (id,"n")
// (sc,";")
// (id,"minus1")
// (op,":=")
// (d,"0")
// (sc,";")
// (id,"minus2")
// (op,":=")
// (d,"1")
// (sc,";")
// (key,"while")
// (id,"n")
// (op,">")
// (d,"0")
// (key,"do")
// (p,"{")
// (id,"temp")
// (op,":=")
// (id,"minus2")
// (sc,";")
// (id,"minus2")
// (op,":=")
// (id,"minus1")
// (op,"+")
// (id,"minus2")
// (sc,";")
// (id,"minus1")
// (op,":=")
// (id,"temp")
// (sc,";")
// (id,"n")
// (op,":=")
// (id,"n")
// (op,"-")
// (d,"1")
// (p,"}")
// (sc,";")
// (key,"write")
// (str,"\"Result: \"")
// (sc,";")
// (key,"write")
// (id,"minus2")
// (sc,";")
// (key,"write")
// (str,"\"\\n\"")


///////////////////////////////////////////////////////////////
val prog2 = """
start := 1000;
x := start;
y := start;
z := start;
while 0 < x do {
while 0 < y do {
while 0 < z do { z := z - 1 };
z := start;
y := y - 1
};
y := start;
x := x - 1
}
"""

@arg(doc = "Three‑nested‑loops test")
@main
def loops() = {
  println("lexing three nested loops program")
  println(escape(lexing_simp(WHILE_REGS, prog2)).mkString("\n"))
}

// (id,"start")
// (op,":=")
// (nr,"1000")
// (sc,";")
// (id,"x")
// (op,":=")
// (id,"start")
// (sc,";")
// (id,"y")
// (op,":=")
// (id,"start")
// (sc,";")
// (id,"z")
// (op,":=")
// (id,"start")
// (sc,";")
// (key,"while")
// (d,"0")
// (op,"<")
// (id,"x")
// (key,"do")
// (p,"{")
// (key,"while")
// (d,"0")
// (op,"<")
// (id,"y")
// (key,"do")
// (p,"{")
// (key,"while")
// (d,"0")
// (op,"<")
// (id,"z")
// (key,"do")
// (p,"{")
// (id,"z")
// (op,":=")
// (id,"z")
// (op,"-")
// (d,"1")
// (p,"}")
// (sc,";")
// (id,"z")
// (op,":=")
// (id,"start")
// (sc,";")
// (id,"y")
// (op,":=")
// (id,"y")
// (op,"-")
// (d,"1")
// (p,"}")
// (sc,";")
// (id,"y")
// (op,":=")
// (id,"start")
// (sc,";")
// (id,"x")
// (op,":=")
// (id,"x")
// (op,"-")
// (d,"1")
// (p,"}")



///////////////////////////////////////////////////////////////
val prog3 = """
// Find all factors of a given input number
write "Input n please: ";
read n;
write "The factors of n are: \n";
f := 2;
while (f < n / 2 + 1) do {
if ((n / f) * f == n)
then { write(f); write("\n") }
else { skip };
f := f + 1
}
"""

@arg(doc = " Factors test")
@main
def fact() = {
  println("lexing factors program")
  println(escape(lexing_simp(WHILE_REGS, prog3)).mkString("\n"))
}

// (comm,"// Find all factors of a given input number\n")
// (key,"write")
// (str,"\"Input n please: \"")
// (sc,";")
// (key,"read")
// (id,"n")
// (sc,";")
// (key,"write")
// (str,"\"The factors of n are: \\n\"")
// (sc,";")
// (id,"f")
// (op,":=")
// (d,"2")
// (sc,";")
// (key,"while")
// (p,"(")
// (id,"f")
// (op,"<")
// (id,"n")
// (op,"/")
// (d,"2")
// (op,"+")
// (d,"1")
// (p,")")
// (key,"do")
// (p,"{")
// (key,"if")
// (p,"(")
// (p,"(")
// (id,"n")
// (op,"/")
// (id,"f")
// (p,")")
// (op,"*")
// (id,"f")
// (op,"==")
// (id,"n")
// (p,")")
// (key,"then")
// (p,"{")
// (key,"write")
// (p,"(")
// (id,"f")
// (p,")")
// (sc,";")
// (key,"write")
// (p,"(")
// (str,"\"\\n\"")
// (p,")")
// (p,"}")
// (key,"else")
// (p,"{")
// (key,"skip")
// (p,"}")
// (sc,";")
// (id,"f")
// (op,":=")
// (id,"f")
// (op,"+")
// (d,"1")
// (p,"}")

///////////////////////////////////////////////////////////////
val prog4 = """
// Collatz series
//
// needs writing of strings and numbers; comments
bnd := 1;
while bnd < 101 do {
write bnd;
write ": ";
n := bnd;
cnt := 0;
while n > 1 do {
write n;
write ",";
if n % 2 == 0
then n := n / 2
else n := 3 * n+1;
cnt := cnt + 1
};
write " => ";
write cnt;
write "\n";
bnd := bnd + 1
}
"""

@arg(doc = " Collatz test")
@main
def collatz() = {
  println("lexing Collatz program")
  println(escape(lexing_simp(WHILE_REGS, prog4)).mkString("\n"))
}

// (comm,"// Collatz series\n")
// (comm,"//\n")
// (comm,"// needs writing of strings and numbers; comments\n")
// (id,"bnd")
// (op,":=")
// (d,"1")
// (sc,";")
// (key,"while")
// (id,"bnd")
// (op,"<")
// (nr,"101")
// (key,"do")
// (p,"{")
// (key,"write")
// (id,"bnd")
// (sc,";")
// (key,"write")
// (str,"\": \"")
// (sc,";")
// (id,"n")
// (op,":=")
// (id,"bnd")
// (sc,";")
// (id,"cnt")
// (op,":=")
// (d,"0")
// (sc,";")
// (key,"while")
// (id,"n")
// (op,">")
// (d,"1")
// (key,"do")
// (p,"{")
// (key,"write")
// (id,"n")
// (sc,";")
// (key,"write")
// (str,"\",\"")
// (sc,";")
// (key,"if")
// (id,"n")
// (op,"%")
// (d,"2")
// (op,"==")
// (d,"0")
// (key,"then")
// (id,"n")
// (op,":=")
// (id,"n")
// (op,"/")
// (d,"2")
// (key,"else")
// (id,"n")
// (op,":=")
// (d,"3")
// (op,"*")
// (id,"n")
// (op,"+")
// (d,"1")
// (sc,";")
// (id,"cnt")
// (op,":=")
// (id,"cnt")
// (op,"+")
// (d,"1")
// (p,"}")
// (sc,";")
// (key,"write")
// (str,"\" => \"")
// (sc,";")
// (key,"write")
// (id,"cnt")
// (sc,";")
// (key,"write")
// (str,"\"\\n\"")
// (sc,";")
// (id,"bnd")
// (op,":=")
// (id,"bnd")
// (op,"+")
// (d,"1")
// (p,"}")




