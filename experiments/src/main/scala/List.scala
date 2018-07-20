import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object List{

  val list = FreshIdentifier("List")
  val cons = FreshIdentifier("Cons")
  val nil = FreshIdentifier("Nil")

  val head = FreshIdentifier("head")
  val tail = FreshIdentifier("tail")

  val listADT = mkSort(list)("A")(Seq(cons, nil))
  val nilADT = mkConstructor(nil)("A")(Some(list))(_ => Seq())
  val consADT = mkConstructor(cons)("A")(Some(list)) { case Seq(aT) =>
    Seq(ValDef(head, aT), ValDef(tail, T(list)(aT)))
  }

  val lengthID = FreshIdentifier("len")
  val lengthFunction: FunDef = mkFunDef(lengthID)("A"){ case Seq(aT) =>
    val args: Seq[ValDef] = Seq("l" :: T(list)(aT))
    val retType: Type = IntegerType
    val body: Seq[Variable] => Expr = { case Seq(l) =>
      if_ (l.isInstOf(T(cons)(aT))) {
        E(BigInt(1)) + E(lengthID)(aT)(l.asInstOf(T(cons)(aT)).getField(tail))
      } else_ { // nil
        E(BigInt(0))
      }
    }

    (args, retType, body)
  }

  val subtermID = FreshIdentifier("sub")
  val subtermFunction: FunDef = mkFunDef(subtermID)("A"){ case Seq(aT) =>
    val args: Seq[ValDef] = Seq("x"::T(list)(aT),"y" :: T(list)(aT))
    val retType: Type = BooleanType
    val body: Seq[Variable] => Expr = { case Seq(x,y) =>
      if_ (y.isInstOf(T(cons)(aT))) {
        x.asInstOf(T(cons)(aT)) === y.asInstOf(T(cons)(aT)).getField(tail)
      } else_ { // nil
        x.isInstOf(T(nil)(aT))
      }
    }

    (args, retType, body)
  }

  val linearRevID = FreshIdentifier("linearRev")
  val linearRevFunction: FunDef = mkFunDef(linearRevID)("A"){ case Seq(aT) =>
    val args: Seq[ValDef] = Seq("x" :: T(list)(aT),"y" :: T(list)(aT))
    val retType: Type = T(list)(aT)
    val body: Seq[Variable] => Expr = { case Seq(x,y) =>
      if_ (x.isInstOf(T(nil)(aT))) {
        y
      } else_ { // cons
        E(linearRevID)(aT)(x.asInstOf(T(cons)(aT)).getField(tail), 
                           T(cons)(aT)(x.asInstOf(T(cons)(aT)).getField(head),y))
      }
    }

    (args, retType, body)
  }

  val appendID = FreshIdentifier("append")
  val appendFunction: FunDef = mkFunDef(appendID)("A"){ case Seq(aT) =>
    val args: Seq[ValDef] = Seq("x" :: T(list)(aT),"y" :: T(list)(aT))
    val retType: Type = T(list)(aT)
    val body: Seq[Variable] => Expr = { case Seq(x,y) =>
      if_ (x.isInstOf(T(nil)(aT))) {
        y
      } else_ { // cons
        T(cons)(aT)(x.asInstOf(T(cons)(aT)).getField(head),
                    E(appendID)(aT)(x.asInstOf(T(cons)(aT)).getField(tail),y))       
      }
    }

    (args, retType, body)
  }

  val revID = FreshIdentifier("rev")
  val revFunction: FunDef = mkFunDef(revID)("A"){ case Seq(aT) =>
    val args: Seq[ValDef] = Seq("l" :: T(list)(aT))
    val retType: Type = T(list)(aT)
    val body: Seq[Variable] => Expr = { case Seq(l) =>
      if_ (l.isInstOf(T(nil)(aT))) {
        T(nil)(aT)()
      } else_ { // cons
        E(appendID)(aT)(E(revID)(aT)(l.asInstOf(T(cons)(aT)).getField(tail)),
                        T(cons)(aT)(l.asInstOf(T(cons)(aT)).getField(head),T(nil)(aT)()))
      }
    }

    (args, retType, body)
  }

  val len = E(lengthID)
  val subterm = E(subtermID)
  val linearRev = E(linearRevID)
  val append = E(appendID)
  val rev = E(revID)

  
}
