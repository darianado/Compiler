
// Simple Version for WHILE-language
//====================================
//
//
//  Lexer + Parser + Interpreter


// Lexer for WHILE langaige
//////////////////////////////////////////////////////////////////////////
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

def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.collect{ 
    // case ("w",_) => None
    case (s1, s2) if s1!="w" && s1!="comm"  => (s1, s2)
    }


abstract class Token
case class T_Key(s:String) extends Token
case class T_Comm(s:String) extends Token
case class T_Op(s:String) extends Token
case class T_Id(s:String) extends Token
case class T_Sc(s:String) extends Token
case class T_Symb(s:String) extends Token
case class T_Str(s:String) extends Token
case class T_Ws(s:String) extends Token
case class T_Dig(s:String) extends Token
case class T_Paren(s:String) extends Token
case class T_Nr(s:String) extends Token


def pairToToken(p:(String,String)): Token = p match{
  case (l,k)=> l match{
    case "key"=>T_Key(k)
    case "comm"=> T_Comm(k)
    case "op"=> T_Op(k)
    case "id"=> T_Id(k)
    case "sc"=> T_Sc(k)
    case "symb"=> T_Symb(k)
    case "str"=> T_Str(k.substring(1, k.length()-1))
    case "w"=> T_Ws(k)
    case "d"=> T_Dig(k)
    case "p"=> T_Paren(k)
    case "nr"=> T_Nr(k)
  }
  
} 

def makeTokens(s: Seq[(String,String)]) : Seq[Token] = {
  s.map(pairToToken)
}


// Parser for the WHILE language
///////////////////////////////////////////////////////////////////////////


{
case class ~[+A, +B](x: A, y: B)

// constraint for the input
type IsSeq[A] = A => Seq[_]


abstract class Parser[I : IsSeq, T]{
  def parse(in: I): Set[(T, I)]

  def parse_all(in: I) : Set[T] =
    for ((hd, tl) <- parse(in); 
        if tl.isEmpty) yield hd
}

// parser combinators

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(in: I) = 
    for ((hd1, tl1) <- p.parse(in); 
         (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], 
                              q: => Parser[I, T]) extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)   
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 f: T => S) extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}


case class OpParser(s:String) extends Parser[Seq[Token],String]{

  def parse(st: Seq[Token])= st match{
    case x +: xs=> {x match{
      case T_Op(o)=> if (o==s) {Set((o,xs))} else Set()
      case _ => Set()
    }}
    case Nil => Set()
  }

}

case class ParenParser(s:String) extends Parser[Seq[Token],String]{

  def parse(st: Seq[Token])= st match{
    case x +: xs=> {x match{
      case T_Paren(o)=> if (o==s) Set((o,xs)) else Set()
      case _ => Set()
    }}
    case Nil => Set()
  }

}

case object ScParser extends Parser[Seq[Token],String]{

  def parse(st: Seq[Token])= st match{
    case x +: xs=> {x match{
      case T_Sc(o)=> if (o==";") Set((o,xs)) else Set()
      case _ => Set()
    }}
    case Nil => Set()
  }

}

case class KeyParser(s:String) extends Parser[Seq[Token],String]{

  def parse(st: Seq[Token])= st match{
    case x +: xs=> {x match{
      case T_Key(o)=> if (o==s) Set((o,xs)) else Set()
      case _ => Set()
    }}
    case Nil => Set()
  }

}

case object IdParser extends Parser[Seq[Token],String]{

 def parse(st: Seq[Token])= st match{
    case x +: xs=> {x match{
      case T_Id(o)=>  Set((o,xs))
      case _ => Set()
    }}
    case Nil => Set()
  }

}

case object NumParser extends Parser[Seq[Token], Int] {

  def parse(st: Seq[Token]) = st match {
    case x +: xs=> {x match{
      case T_Dig(o)=>  Set((o.toInt,xs))
      case T_Nr(o)=> Set((o.toInt,xs))
      case _ => Set()
    }}
    case Nil => Set()
    
  }

}

case object StrParser extends Parser[Seq[Token], String] {

  def parse(st: Seq[Token]) = st match {
    case x +: xs=> {x match{
      case T_Str(o)=>  Set((o,xs))
      case _ => Set()
    }}
    case Nil => Set()
    
  }

}  

// more convenient syntax for parser combinators
implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}

// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp 

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Write(s: String) extends Stmt
case class Read(s: String) extends Stmt

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp


// arithmetic expressions
lazy val AExp: Parser[Seq[Token], AExp] = 
  (Te ~ OpParser("+") ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("+", x, z) } ||
  (Te ~ OpParser("-") ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("-", x, z) } || Te
lazy val Te: Parser[Seq[Token], AExp] = 
  (Fa ~ OpParser("*") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("*", x, z) } ||
  (Fa ~ OpParser("%") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("%", x, z) } || 
  (Fa ~ OpParser("/") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("/", x, z) } || Fa  
lazy val Fa: Parser[Seq[Token], AExp] = 
   (ParenParser("(") ~ AExp ~ ParenParser(")")).map{ case _ ~ y ~ _ => y } || 
   IdParser.map(Var) || 
   NumParser.map(Num)

// boolean expressions with some simple nesting
lazy val BExp: Parser[Seq[Token], BExp] = 
   (El ~ OpParser("&&") ~ BExp).map[BExp]{ case  y ~ _ ~ v => And(y, v) } ||
   (El ~ OpParser("||") ~ BExp).map[BExp]{ case  y ~  _ ~ v => Or(y, v) } || El
lazy val El: Parser[Seq[Token], BExp] = 
   (AExp ~ OpParser("==") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("==", x, z) } || 
   (AExp ~ OpParser("!=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("!=", x, z) } || 
   (AExp ~ OpParser("<") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z) } || 
   (AExp ~ OpParser(">") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">", x, z) } ||
   (AExp ~ OpParser("<=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<=", x, z) } || 
   (AExp ~ OpParser(">=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">=", x, z) } ||
   (KeyParser("true").map[BExp]{ _ => True }) || 
   (KeyParser("false").map[BExp]{ _ => False }) ||
   (ParenParser("(") ~ BExp ~ ParenParser(")")).map[BExp]{ case _ ~ x ~ _ => x }

// a single statement 
lazy val Stmt: Parser[Seq[Token], Stmt] =
  ((KeyParser("skip").map[Stmt]{_ => Skip }) ||
   (IdParser ~ OpParser(":=") ~ AExp).map[Stmt]{ case x ~ _ ~ z => Assign(x, z) } ||
   (KeyParser("write")~ ParenParser("(") ~ IdParser ~ ParenParser(")")).map[Stmt]{ case _ ~ _ ~ y ~ _ => Write(y) } ||
   (KeyParser("write") ~ ParenParser("(") ~ StrParser  ~ ParenParser(")") ).map[Stmt]{ case _ ~_ ~ y ~_ => Write(y) } ||
   (KeyParser("write") ~ StrParser ).map[Stmt]{ case _ ~ y => Write(y) } ||
   (KeyParser("write") ~ IdParser ).map[Stmt]{ case _ ~ y => Write(y) } ||
   (KeyParser("read") ~ IdParser ).map[Stmt]{ case _ ~ y => Read(y) } ||
   (KeyParser("if") ~ BExp ~ KeyParser("then") ~ Block ~ KeyParser("else") ~ Block)
     .map[Stmt]{ case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w) } ||
   (KeyParser("while") ~ BExp ~ KeyParser("do") ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ w => While(y, w) }
   )   
 
// statements
lazy val Stmts: Parser[Seq[Token], Block] =
  (Stmt ~ ScParser ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) })

// blocks (enclosed in curly braces)
lazy val Block: Parser[Seq[Token], Block] =
  ((ParenParser("{") ~ Stmts ~ ParenParser("}")).map{ case _ ~ y ~ _ => y } || 
   (Stmt.map(s => List(s))))

}


// TEST parsing on the 4 programs

val f = """if (a < b) then skip else a := a * b + 1"""

// print(Stmts.parse_all(makeTokens(escape(lexing_simp(WHILE_REGS, f)))))

val fib = """write "Fib: ";
read n;
minus1 := 1;
minus2 := 0;
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

// print(Stmts.parse_all(makeTokens(escape(lexing_simp(WHILE_REGS, fib))))) 

val loops = """start := 500;
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

// print(Stmts.parse_all(makeTokens(escape(lexing_simp(WHILE_REGS, loops)))))

val prims = """// prints out prime numbers from 2 to 100
end := 100;
n := 2;
while (n < end) do {
f := 2;
tmp := 0;
while ((f < n / 2 + 1) && (tmp == 0)) do {
if ((n / f) * f == n) then { tmp := 1 } else { skip };
f := f + 1
};
if (tmp == 0) then { write(n); write("\n") } else { skip };
n := n + 1
}
"""

// print(Stmts.parse_all(makeTokens(escape(lexing_simp(WHILE_REGS, prims)))))

val collat = """// Collatz series
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

// print(Stmts.parse_all(makeTokens(escape(lexing_simp(WHILE_REGS, collat)))))



// ////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Interpreter for the WHILE language
type Env = Map[String, Int]

def eval_aexp(a: AExp, env: Env) : Int = a match {
  case Num(i) => i
  case Var(s) => env(s)
  case Aop("+", a1, a2) => eval_aexp(a1, env) + eval_aexp(a2, env)
  case Aop("-", a1, a2) => eval_aexp(a1, env) - eval_aexp(a2, env)
  case Aop("*", a1, a2) => eval_aexp(a1, env) * eval_aexp(a2, env)
  case Aop("/", a1, a2) => eval_aexp(a1, env) / eval_aexp(a2, env)
  case Aop("%", a1, a2) => eval_aexp(a1, env) % eval_aexp(a2, env)
}

def eval_bexp(b: BExp, env: Env) : Boolean = b match {
  case True => true
  case False => false
  case Bop("==", a1, a2) => eval_aexp(a1, env) == eval_aexp(a2, env)
  case Bop("!=", a1, a2) => !(eval_aexp(a1, env) == eval_aexp(a2, env))
  case Bop(">", a1, a2) => eval_aexp(a1, env) > eval_aexp(a2, env)
  case Bop("<", a1, a2) => eval_aexp(a1, env) < eval_aexp(a2, env)
  case Bop(">=", a1, a2) => eval_aexp(a1, env) >= eval_aexp(a2, env)
  case Bop("<=", a1, a2) => eval_aexp(a1, env) <= eval_aexp(a2, env)
  case And(b1, b2) => eval_bexp(b1, env) && eval_bexp(b2, env)
  case Or(b1, b2) => eval_bexp(b1, env) || eval_bexp(b2, env)
}

import scala.io.StdIn.readInt

{
def eval_stmt(s: Stmt, env: Env) : Env = s match {
  case Skip => env
  case Assign(x, a) => env + (x -> eval_aexp(a, env))
  case If(b, bl1, bl2) => if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env) 
  case While(b, bl) => 
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env))
    else env
  case Write(x) => { 
                      if ( !env.exists(_._1 == x)) // printing a string
                        {
                          if(x=="""\n""") print ('\n') //proper new line printing
                          else print(x); 
                          env
                        }
                     else print(env(x)) ; env // printing a value from the environment
                    } 
  case Read(x) =>  {val n=readInt(); env + (x-> n)}
}

def eval_bl(bl: Block, env: Env) : Env = bl match {
  case Nil => env
  case s::bl => eval_bl(bl, eval_stmt(s, env))
}
}

def eval(bl: Block) : Env = eval_bl(bl, Map())


//TEST eval on the 4 programs

// println(eval(Stmts.parse_all(makeTokens(escape(lexing_simp(WHILE_REGS, fib)))).head))

// val pre = System.nanoTime()
// println(eval(Stmts.parse_all(makeTokens(escape(lexing_simp(WHILE_REGS, loops)))).head))
// val after = System.nanoTime()
// print((after-pre)/ 1_000_000_000)//seconds

// println(eval(Stmts.parse_all(makeTokens(escape(lexing_simp(WHILE_REGS, prims)))).head))

// println(eval(Stmts.parse_all(makeTokens(escape(lexing_simp(WHILE_REGS, collat)))).head))



// runs with amm2 and amm3
