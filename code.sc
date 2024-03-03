
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case object ALL extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class RANGE(s: Set[Char]) extends Rexp 
case class PLUS(r: Rexp) extends Rexp 
case class OPTIONAL(r: Rexp) extends Rexp 
case class UPTO(r: Rexp, m: Int) extends Rexp
case class FROM(r: Rexp, n: Int) extends Rexp
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp
case class NOT(r: Rexp) extends Rexp
case class CFUN(f: Char => Boolean) extends Rexp


def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case CHAR(char) => CFUN( (c:Char) => if(char==c) true else false )
  case RANGE(s) => CFUN( (c:Char) =>  if(s(c)) true else false ) 
  case ALL => CFUN( (c:Char) => true )
  case r => r
}

// the nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = {r match {
  case ZERO => false
  case ONE => true
  // case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case NTIMES(r1, i) => if (i == 0) true else nullable(r1)
  // case RANGE(s) => false
  case PLUS(r1) => nullable(r1)
  case OPTIONAL(r1) => true
  case UPTO(r1, m) => true
  case FROM(r1,n) => if(n==0) true else nullable(r1)
  case BETWEEN(r1,n,m) => if(n==0) true else nullable(r1)
  case NOT(r1) => if (nullable(r1)) false else true
  case CFUN(f) => false
  // case ALL => false
  case _ => nullable(simp(r)) // to simplify any CHAR RANGE or ALL into CFUN
}
}

// the derivative of a regular expression w.r.t. a character
def der(c: Char, r: Rexp) : Rexp = {r match {
  case ZERO => ZERO
  case ONE => ZERO
  // case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
                    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
                    else SEQ(der(c, r1), r2)
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))
  case NTIMES(r, i) => 
                      if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
  // case RANGE(s) => if(s(c)) ONE else ZERO //if set contains the char
  case PLUS(r1) => SEQ(der(c,r1),STAR(r1))
  case OPTIONAL(r1) => der(c,r1)// + 0
  case UPTO(r1, m) => if(m==0) ZERO else SEQ(der(c,r1),UPTO(r1,m-1))
  case FROM(r1,n) => if(n==0) ZERO else SEQ(der(c,r1),FROM(r1,n-1))
  case BETWEEN(r1,n,m) => if(n==m) NTIMES(r,n)
                          else if (n==0) SEQ(der(c,r1),UPTO(r1,m-1)) 
                                else SEQ(der(c,r1), BETWEEN(r1, n-1,m-1))
  case NOT(r1) => NOT(der(c,r1))
  case CFUN(f) => if(f(c)==true) ONE else ZERO
  // case ALL => ONE
  case _ => der(c,simp(r)) // if not one of the options it can be simplified in CFUN
}}


// the derivative w.r.t. a string (iterates der)
def ders(s: List[Char], r: Rexp) : Rexp = {s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}}


// the main matcher function32
def matcher(r: Rexp, s: String) : Boolean = {
  nullable(ders(s.toList, simp(r)))}



//Q3
//////////////////////////////////////////

matcher(OPTIONAL(CHAR('a')),"aaaaaa")
matcher(NOT(CHAR('a')),"aaaaaa")
matcher(NTIMES(CHAR('a'),3),"aaaaaa")
matcher(NTIMES(OPTIONAL(CHAR('a')),3),"aaaaaa")
matcher(UPTO(CHAR('a'),3),"aaaaaa")
matcher(UPTO(OPTIONAL(CHAR('a')),3),"aaaaaa")
matcher(BETWEEN(CHAR('a'),3,5),"aaaaaa")
matcher(BETWEEN(OPTIONAL(CHAR('a')),3,5),"aaaaaa")

//Q5
//////////////////////////////////////////

val kcl = SEQ(SEQ(SEQ(
            SEQ(PLUS(RANGE("abcdefghijklmnopqrstuvwxyz0123456789_.-".toSet)),CHAR('@') )
          , PLUS(RANGE("abcdefghijklmnopqrstuvwxyz0123456789.-".toSet))), CHAR('.') )
          , BETWEEN(RANGE("abcdefghijklmnopqrstuvwxyz.".toSet),2,6) )
// true
matcher(kcl , "dariana.dorin@kcl.ac.uk" )

// ( [a-z0-9.-]* . "." . [a-z.]{2...6} ) + [a-z.]{0...4} + [a-z.]{...1} 
ders("dariana.dorin@kcl.ac.uk".toList, kcl)

//Q6
//////////////////////////////////////////

val re= SEQ(SEQ(SEQ(CHAR('/'),CHAR('*')),
             NOT(SEQ(SEQ(SEQ( STAR(ALL) , CHAR('*') ), CHAR('/')  ), STAR(ALL) ) ) ),
              SEQ(CHAR('*'),CHAR('/')))

matcher(re, "/**/") //yes
matcher(re, "/*foobar*/")  //yes
matcher(re, "/*test*/test*/") //no
matcher(re, "/*test/*test*/")  //yes

//Q7
//////////////////////////////////////////

val r1 = SEQ(SEQ(CHAR('a'),CHAR('a')),CHAR('a'))
val r2 = SEQ(BETWEEN(CHAR('a'),19,19), OPTIONAL(CHAR('a')))

//120 a - r1 yes , r2 no
matcher( PLUS(PLUS(r1)), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" )
matcher( PLUS(PLUS(r2)), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" )
//131 a - r1 no , r2 no 
matcher( PLUS(PLUS(r1)), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
matcher( PLUS(PLUS(r2)), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
//136 a - r1 no , r2 no
matcher( PLUS(PLUS(r1)), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
matcher( PLUS(PLUS(r2)), "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
