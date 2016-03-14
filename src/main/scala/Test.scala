import scala.meta._
import scala.meta.internal.ast.Defn
import scala.meta.tql._

object Test {
  def main(args: Array[String]): Unit = {
    val stream = getClass.getResourceAsStream("MutRec.scala")
    val tree = stream.parse[Source]

    /*
    val tree1 = tree.transform {
      case q"..$mods def $name[..$tparams](...$paramss): $tpeopt = $expr" =>
        val (tparams1, evidences) = tparams.transform {
          case tparam"..$mods $name[..$tparams] >: $lo <: $hi <% ..$vbs : ..$cbs" =>
            val paramEvidences = vbs.map(vb => {
              val evidenceName = Term.fresh("ev")
              val evidenceTpe = name match {
                case name: Type.Name =>
                  t"$name => $vb"
                case name: Name.Anonymous =>
                  // NOTE: These type parameters are bugged in scalac, so we bail.
                  val msg = "can't rewrite context-bounded anonymous type parameters"
                  sys.error(s"error at ${name.position}:\n$msg")
              }
              param"implicit $evidenceName: $evidenceTpe"
            })
            val tparam1 = tparam"..$mods $name[..$tparams] >: $lo <: $hi : ..$cbs"
            tparam1 withResult paramEvidences
        }
        val paramss1 = {
          if (evidences.isEmpty) paramss
          else {
            def isImplicit(p: Term.Param) = {
              val param"..$mods $_: $_ = $_" = p
              mods.collect{ case mod"implicit" => }.nonEmpty
            }
            val shouldMerge = paramss.nonEmpty && paramss.last.exists(isImplicit)
            if (shouldMerge) paramss.init :+ (paramss.last ++ evidences)
            else paramss :+ evidences
          }
        }
        q"..$mods def $name[..$tparams1](...$paramss1): $tpeopt = $expr"
    }
    println(tree1)
    */

    /*
    val res3 = tree.collect {
      case q"..$mods def $name[..$tparams](...$paramss): $tpeopt = $expr" =>
        name
    }
    println(res3)

    //println(tree.show[Structure])

    tree match {
      case source"$mainObj" => mainObj match {
        case q"object $mainObjName extends ${template"{ $param => ..$stats2 }"}" =>
        //case q"object $mainObjName extends ${template"{ ..$stats1 } with ..$ctorcalls { $param => ..$stats2 }"}" =>
          println(stats2.show[Structure])

      }

        //println(mainObj.show[Structure])
    }

    tree match {
      case source"""
        object $mainObjName { $mainObjSelfName =>
          ..$stats
          def run(): $retTp = $body
        }"""
        =>
        //case q"object $mainObjName extends ${template"{ ..$stats1 } with ..$ctorcalls { $param => ..$stats2 }"}" =>
        println(stats.show[Structure])
        println(retTp.show[Structure])
        println(body.show[Structure])

      //println(mainObj.show[Structure])
    }
    */

    val o: Val = tree match {
      case source"$mainObjDef" => mainObjDef match {
        case mainObj: Defn.Object => translateObject(mainObj)
      }
    }
    val t = Let("mainObj", o, App(PthSel(PthVar("mainObj"), "run"), PthVar("unit")))
    println(t)
  }

  implicit def termNameToString(n: Term.Name): String = n.toString()
  implicit def typeNameToString(n: Type.Name): String = n.toString()
  implicit def termParamNameToString(n: Term.Param.Name): String = n.toString()

  // https://github.com/scalameta/scalameta/blob/master/docs/quasiquotes.md

  def translateTerm(t: Term): Trm = t match {
    case name: Term.Name => PthVar(name.toString())
    case p @ q"$pth.$name" => translateTermPath(p)
    case q"$expr: $tpe" => ??? // TODO


    // 1) Matching Applications

    // that's what I'd like to write, but it doesn't work :(
    case q"$expr($aexpr)" =>
      val f: Term = expr
      val a: Term = aexpr // ERROR: found Term.Arg, required: Term
      App(translateTerm(f), translateTerm(a))

    // ok so we have to do this, but that's so long :(
    case q"$expr($aexpr)" =>
      (aexpr: Term.Arg) match {
        case arg"${expr2: Term}" => App(translateTerm(expr), translateTerm(expr2))
      }

    // put both matches on one line. Q: Can we do this more nicely?
    case q"$expr(${arg"${expr2: Term}"})" => App(translateTerm(expr), translateTerm(expr2))


    // 2) Matching Lambdas

    // that's what I'd like to write, but I get
    // ERROR: ; expected but right arrow found
    case q"($argName: $argType) => $body" => Lambda(argName, translateType(argType), translateTerm(body))

    // ok so like this, it works, but that's too long :(
    case q"($param) => $expr" => param match {
      case param"..$mods $paramname: $atpeopt = $expropt" => atpeopt match {
        case Some(targ"${tpe: Type}") => Lambda(paramname, translateType(tpe), translateTerm(expr))
      }
    }

    // slightly shorter, but still not happy :(
    case q"(${param"$paramname: $atpeopt"}) => $expr" => atpeopt match {
      case Some(targ"${tpe: Type}") => Lambda(paramname, translateType(tpe), translateTerm(expr))
    }


    // 3) Matching "new"

    // that's what I'd like to write, but $selfName is a Term.Param (including a type), not just a name
    case q"new { $selfName => ..$defs }" => New(TypTop /* TODO */, selfName, defs.map(translateDefn))

    // this works, but again, quite long :(
    case q"new { $selfParam => ..$defs }" => selfParam match {
      case param"$selfParamName: $selfType" => selfType match {
        case Some(_) => sys.error("unsupported")
        case None => New(TypTop /* TODO */, selfParamName, defs.map(translateDefn))
      }
    }

  }

  def translateType(t: Type): Typ = t match {
    case t"Any" => TypTop
    case t"Bot" => TypBot
    case t"$ref.$tname" => TypSel(translateTypePath(ref), tname)
    case t"$t1 => $t2" => TypAll("dummy", translateType(t1), translateType(t2))
  }

  def translateTypePath(p: Type): Pth = p match {
    case t"$ref.$fieldName" => PthSel(translateTypePath(ref), fieldName)
    case t"$ref" => PthVar(ref)
  }

  def translateTermPath(p: Term): Pth = p match {
    case q"$ref.$fieldName" => PthSel(translateTermPath(ref), fieldName)
    case q"$ref" => PthVar(ref)
  }

  def translateDefn(s: Stat): Def = s match {
    case d @ q"def $name(): $tp = $body" =>
      DefVal(name, Lambda("dummy", TypTop, translateTerm(body)))
    case d @ q"type $tname = $tp" =>
      DefTyp(tname, translateType(tp))
    case d @ q"class $cname { $selfName => ..$defs }" =>
      DefVal(cname, translateClass(d))
    case d @ q"object $name { $selfName => ..$defs }" =>
      DefVal(name, translateObject(d))
  }

  def translateClass(d: Defn.Class): Val = d match {
    case q"class $cname { $selfName => ..$defs }" => DefVal(cname, New(TypTop /*TODO*/, cname,
      DefTyp("C", TypTop /*TODO*/) +:
      defs.map(translateDefn)
    ))
  }

  def translateObject(d: Defn.Object): Val = d match {
    case q"object $name { $selfName => ..$defs }" => DefVal(name, New(TypTop /*TODO*/ , name, defs.map(translateDefn)))
  }

  // package/package object similar
  // val not yet supported (use def or object instead), because expr on rhs is problematic
  // trait not yet supported (only classes)
  // constructors and vars not yet supported
  // macros not yet supported




  // DOT

  sealed trait Trm

  case class App(func: Trm, arg: Trm) extends Trm

  case class Let(name: String, t1: Trm, t2: Trm) extends Trm

  trait Val extends Trm
  case class New(typ: Typ, selfName: String, defs: Seq[Def]) extends Val
  case class Lambda(argName: String, argTyp: Typ, body: Trm) extends Val

  sealed trait Def
  case class DefTyp(name: String, typ: Typ) extends Def
  case class DefVal(name: String, rhs: Val) extends Def

  trait Pth extends Trm
  case class PthVar(name: String) extends Pth
  case class PthSel(prefix: Pth, sel: String) extends Pth

  sealed trait Typ
  case object TypTop extends Typ
  case object TypBot extends Typ
  case class TypRcd(dec: Dec) extends Typ
  case class TypAnd(l: Typ, r: Typ) extends Typ
  case class TypSel(prefix: Pth, sel: String) extends Typ
  case class TypBnd(selfName: String, typ: Typ) extends Typ
  case class TypAll(argName: String, argTyp: Typ, retTyp: Typ) extends Typ

  sealed trait Dec
  case class DecTyp(name: String, lo: Typ, hi: Typ) extends Dec
  case class DecVal(name: String, typ: Typ) extends Dec

}