// A Small LLVM Compiler for a Simple Functional Language
// (includes an external lexer and parser)
//
//
// call with 
//
//     amm fun_llvm.sc main fact.fun
//     amm fun_llvm.sc main defs.fun
//
// or
//en
//     amm fun_llvm.sc write fact.fun
//     amm fun_llvm.sc write defs.fun
//
//       this will generate an .ll file. 
//
// or 
//
//     amm fun_llvm.sc run fact.fun
//     amm fun_llvm.sc run defs.fun
//
//
// You can interpret an .ll file using lli, for example
//
//      lli fact.ll
//
// The optimiser can be invoked as
//
//      opt -O1 -S in_file.ll > out_file.ll
//      opt -O3 -S in_file.ll > out_file.ll
//
// The code produced for the various architectures can be obtain with
//   
//   llc -march=x86 -filetype=asm in_file.ll -o -
//   llc -march=arm -filetype=asm in_file.ll -o -  
//
// Producing an executable can be achieved by
//
//    llc -filetype=obj in_file.ll
//    gcc in_file.o -o a.out
//    ./a.out


import $file.fun_tokens, fun_tokens._
import $file.fun_parser, fun_parser._ 


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}


abstract class Ty
case object TyInt extends Ty
case object TyDouble extends Ty
case object TyVoid extends Ty
case object Undf extends Ty

// Internal CPS language for FUN
abstract class KExp
abstract class KVal

// case class KVar(s: String) extends KVal
case class KVar(s: String , ty: Ty = Undf) extends KVal
case class KNum(i: Int) extends KVal
case class KFNum(d: Double) extends KVal
case class Kop(o: String, v1: KVal, v2: KVal) extends KVal
case class KCall(o: String, vrs: List[KVal]) extends KVal
case class KWrite(v: KVal) extends KVal

case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}
case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}
case class KReturn(v: KVal) extends KExp


// CPS translation from Exps to KExps using a
// continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {
  case Var(s) => k(KVar(s)) 
  case ChConst(s) => k(KNum(s))
  case Num(i) => k(KNum(i))
  case FNum(i) => k(KFNum(i))
  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => KLet(z, Kop(o, y1, y2), k(KVar(z)))))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => 
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))))
  }
  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
      case Nil => {
          val z = Fresh("tmp")
          KLet(z, KCall(name, vs), k(KVar(z)))
      }
      case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
    }
    aux(args, Nil)
  }
  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))
  case Write(e) => {
    val z = Fresh("tmp")
    CPS(e)(y => KLet(z, KWrite(y), k(KVar(z))))
  }
}   

//initial continuation
def CPSi(e: Exp) = CPS(e)(KReturn)

type Env = Map[String, Ty]

def typ_val(v: KVal, ts: Env) :Ty = v match{
  case KVar(s,ty) => 
    if(ts.contains("@"+s)) ts("@"+s)
    else ts.getOrElse(s, ty)
  
  case KNum(_) => TyInt
  case KFNum(_) => TyDouble

  case Kop(o: String, v1: KVal, v2: KVal) => 
    if(!typ_val(v1,ts).equals(typ_val(v2,ts))) 
      { 
        throw new IllegalArgumentException(s"Variables $v1 and $v2 not the same type")
    }else typ_val(v1,ts)
  
  case KCall(x, _) => ts(x)

  case KWrite(v: KVal) => TyVoid
}

def typ_exp(a: KExp, ts: Env) :Ty = a match {
  case KLet(x: String, e1: KVal, e2: KExp) => typ_val(e1,ts)

  case KReturn(v: KVal) => typ_val(v,ts)

  case KIf(x1: String, e1: KExp, e2: KExp) => TyVoid
}



// convenient string interpolations 
// for instructions, labels and methods
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def sring_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
    def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}


// mathematical and boolean operations
def compile_op(op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "/" => "sdiv i32 "
  case "%" => "srem i32 "
  case "==" => "icmp eq i32 "
  case "!=" => "icmp ne i32 "
  case "<=" => "icmp sle i32 "     // signed less or equal
  case "<"  => "icmp slt i32 "     // signed less than
}

def compile_dop(op: String) = op match {
case "+" => "fadd double "
case "*" => "fmul double "
case "-" => "fsub double "
case "==" => "fcmp oeq double "
case "!=" => "fcmp one double "
case "<=" => "fcmp ole double "
case "<" => "fcmp olt double "
}

def compile_type_toSting(ty: String):String = ty match {
  case "Int" => "i32"
  case "Double" => "double"
  case "Void" => "void"
}

def compile_type_toSting(ty:Ty):String = ty match {
  case TyInt => "i32"
  case TyDouble => "double"
  case TyVoid => "void"
}

def compile_type_toTy(ty:String) :Ty = ty match {
  case "Int" => TyInt
  case "Double" => TyDouble
  case "Void" => TyVoid
}

// chack if a KVal has as a component any global value in the environment
// if yes, returns the decaration of the new local variables referencing
// those globals, the updated KVal with the local variable and the updated env 
def hasGlobal(s:String,v: KVal, env:Env):(String,KVal,Env)={
  v match {
    case KVar(st, ty) =>
      if(env.contains("@"+st))
      {
        val newTemp = Fresh("tmp")
        val typ = env("@"+st)
        val str = m"%$newTemp = load ${compile_type_toSting(typ)},  ${compile_type_toSting(typ)}* @$st"
        val newVar = KVar(newTemp,typ)
        (s+str, newVar , env+(newTemp->typ))
      }
      else
        (s,v,env)

    case Kop(o: String, v1: KVal, v2: KVal)=>
    {
      val (s1,v11,env1)= hasGlobal(s,v1,env)
      val (s2,v22,env2)= hasGlobal(s1,v2,env1)
      (s2,Kop(o,v11,v22),env2)
    }

    case _ =>(s,v,env)
  }
}

// same as hasGlobal but on a list KVal
def hasListGlobal(s:String,args: List[KVal],newArgs:List[KVal], env:Env)
                        :(String,List[KVal],List[KVal],Env)={
  args match{
    case kval::Nil => {
      val (s1, newVal, env1) = hasGlobal("",kval,env)
      (s+s1,args, newArgs:+newVal, env1)
    }
    case kval::tl => {
      val (s1, newVal, env1) = hasGlobal(s,kval,env)
      hasListGlobal(s+s1,tl,newArgs:+newVal,env1)
    }
    case Nil => (s,args, newArgs, env)
  }
}


// compile K values
def compile_val(v: KVal, env: Env) : (String,Env) = v match {
  case KNum(i) => (s"$i",env)
  case KFNum(i) => (s"$i",env)
  case KVar(s, _) => {
    (s"%$s",env)
  }

  case Kop(op, x1, x2) => {
    typ_val(v, env) match{
    case TyInt =>
      (s"${compile_op(op)} ${compile_val(x1,env)._1}, ${compile_val(x2,env)._1}",env)
    case TyDouble =>
      (s"${compile_dop(op)} ${compile_val(x1,env)._1}, ${compile_val(x2,env)._1}",env)
    }
  }

  case KCall(x1, args) => {
    val (addStr, args1 ,newArgs, env1) = hasListGlobal("",args,List(),env)
    
    if(addStr=="") {
      val newArgs=args
      val env1 = env
    }
     
    typ_val(v, env) match{
      case TyInt => 
        (addStr+ (if (addStr != "") "   " else "")+ //ident purpose
          s"call i32 @$x1 (${
            newArgs.map(e=> typ_val(e,env1) match {
            case TyInt => s"i32 ${compile_val(e,env1)._1}"
            case TyDouble => s"double ${compile_val(e,env1)._1}"
          }).mkString(", ")})",env)
      case TyDouble =>
        (addStr+ (if (addStr != "") "   " else "")+ s"call double @$x1 (${
          newArgs.map(e=> typ_val(e,env1) match {
            case TyInt => s"i32 ${compile_val(e,env1)._1}"
            case TyDouble => s"double ${compile_val(e,env1)._1}"
          }).mkString(", ")})", env)
      case TyVoid =>
        (addStr+ (if (addStr != "") "   " else "")+ s"call void @$x1 (${
          newArgs.map(e=> typ_val(e,env1) match {
            case TyInt => s"i32 ${compile_val(e,env1)._1}"
            case TyDouble => s"double ${compile_val(e,env1)._1}"
          }).mkString(", ")})", env)
    }
  }

  case KWrite(x1) =>
    (s"call i32 @printInt (i32 ${compile_val(x1,env)._1})",env)
}

// compile K expressions
def compile_exp(a: KExp, env: Env) : (String,Env) = a match {
  case KReturn(v) =>{ 
    typ_val(v, env) match{
      case TyInt =>
        (i"ret i32 ${compile_val(v,env)._1}",env)
      case TyDouble =>
        (i"ret double ${compile_val(v,env)._1}", env)
      case TyVoid =>
        (i"ret void",env)
    }
  }

  case KLet(x: String, v: KVal, e: KExp) =>{ 
    if(typ_val(v,env)==TyVoid)
    {
      val (valStr, env2) = compile_val(v,env)
      ( i"$valStr" ++
      compile_exp(e, env2 + (x-> typ_val(v,env2)))._1, env)
    }
    else
    {
      val (addStr, newVal, env1) = hasGlobal("",v,env)
      if(addStr!=""){
        val (valStr, env2) = compile_val(newVal,env1)
        ( "   "++addStr ++
          i"%$x = $valStr" ++
          compile_exp(e, env1 + (x-> typ_val(v,env1)))._1, env)
      }
      else{
        val (valStr, env2) = compile_val(v,env)
        ( i"%$x = $valStr" ++
        compile_exp(e, env2 + (x-> typ_val(v,env2)))._1, env)
      }
    }
  }

  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    ( i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1,env)._1 ++
    l"\n$else_br" ++ 
    compile_exp(e2,env)._1 , env )
  }
}


val prelude = """
declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @skip() #0 {
  ret void
}

@.str = private constant [3 x i8] c"%d\00"

define void @print_int(i32 %x) {
   %t0 = getelementptr [3 x i8], [3 x i8]* @.str, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

@.char_str = private constant [3 x i8] c"%c\00"

define void @print_char(i32 %x) {
    %char = trunc i32 %x to i8
    %t0 = getelementptr [3 x i8], [3 x i8]* @.char_str, i32 0, i32 0
    call i32 (i8*, ...) @printf(i8* %t0, i8 %char)
    ret void
}
; END OF BUILD-IN FUNCTIONS (prelude)

"""

//initialise the environment with the funtions in prelude
val globalEnv= Map( 
  "new_line"-> TyVoid,
  "print_star"-> TyVoid,
  "print_space"-> TyVoid,
  "skip"-> TyVoid,
  "print_int"-> TyVoid,
  "print_char"-> TyVoid
)


// compile function for declarations and main
def compile_decl(d: Decl, env: Env) : (String,Env) = d match {
  case Def(name, args, ty , body) => { 
    val curr = name -> compile_type_toTy(ty)

    val param = args.map{
        case (s,"Int") =>  s"i32 %$s"
        case (s,"Double") =>  s"double %$s"
      }.mkString(" ,")

    val localenv = args.map{
      case (s,"Int") =>  s -> TyInt
      case (s,"Double") =>  s-> TyDouble
    }.toMap

    ( m"define ${compile_type_toSting(ty)} @$name ($param) {" ++
    compile_exp( CPSi(body), env ++ localenv + curr )._1 ++
    m"}\n", env + curr )
  }

  case Main(body) => {
    (m"define i32 @main() {" ++
    compile_exp( CPS(body)(_ => KReturn(KNum(0))), env )._1 ++
    m"}\n", env)
  }

  case Const(name, value) => {
    (m"@$name = global i32 $value\n", env + (("@"+name)->TyInt) )
  }

  case FConst(name, value) => {
    (m"@$name = global double $value\n", env +(("@"+name)->TyDouble) )
  }
}

def compile_block(bl: List[Decl], env: Env) : (String, Env) = bl match {
  case Nil => ("", env)
  case s::bl => {
    val (instrs1, env1) = compile_decl(s, env)
    val (instrs2, env2) = compile_block(bl, env1)

    (instrs1 ++ instrs2, env2)
  }
}


// main compiler functions
def compile(prog: List[Decl]) : String = {
  val instructions = compile_block(prog, globalEnv)._1
  (prelude ++ instructions.mkString)
}


// pre-2.5.0 ammonite 
// import ammonite.ops._

// post 2.5.0 ammonite
import os._


@main
def main(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks)
    println(compile(ast))
}

@main
def write(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    println(file)
    val tks = tokenise(os.read(path))
    println(tks)
    val ast = parse_tks(tks)
    println(ast)
    val code = compile(ast)
    println(code)
    os.write.over(os.pwd / (file ++ ".ll"), code)
}

@main
def run(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    write(fname)  
    os.proc("llc", "-filetype=obj", file ++ ".ll").call()
    os.proc("gcc", file ++ ".o", "-o", file ++ ".bin").call()
    os.proc(os.pwd / (file ++ ".bin")).call(stdout = os.Inherit)
    println(s"done.")
}

