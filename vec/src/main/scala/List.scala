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
  
  val contentID = FreshIdentifier("content")
  val contentFunction = mkFunDef(contentID)("A") { case Seq(aT) => 
    val args: Seq[ValDef] = Seq("l" :: T(list)(aT))
    val retType: Type = SetType(aT)
    val body: Seq[Variable] => Expr = { case Seq(l) =>
      if_ (l.isInstOf(T(cons)(aT))) {
        SetAdd(E(contentID)(aT)(l.asInstOf(T(cons)(aT)).getField(tail)), l.asInstOf(T(cons)(aT)).getField(head))
      } else_ {
        FiniteSet(Seq.empty, aT)
      }
    }
    (args, retType, body)
  }

  val memberID = FreshIdentifier("member")
  val memberFunction = mkFunDef(memberID)("A") { case Seq(aT) => 
    val args: Seq[ValDef] = Seq("e" :: aT, "l" :: T(list)(aT))
    val retType: Type = BooleanType
    val body: Seq[Variable] => Expr = { case Seq(e,l) =>
      if_ (l.isInstOf(T(cons)(aT))) {
        val h = l.asInstOf(T(cons)(aT)).getField(head)
        val t = l.asInstOf(T(cons)(aT)).getField(tail)
        (e === h) || E(memberID)(e,t)
      } else_ {
        BooleanLiteral(false)
      }
    }
    (args, retType, body)
  }
  
  val distinctElementsID = FreshIdentifier("distinctElements")
  val distinctElementsFunction: FunDef = mkFunDef(distinctElementsID)("A"){ case Seq(aT) => 
    val args: Seq[ValDef] = Seq("l" :: T(list)(aT))
    val retType: Type = BooleanType
    val body: Seq[Variable] => Expr = { case Seq(l) => 
      if_ (l.isInstOf(T(cons)(aT))) {
        val h = l.asInstOf(T(cons)(aT)).getField(head)
        val t = l.asInstOf(T(cons)(aT)).getField(tail)
        E(distinctElementsID)(t) && !(E(memberID)(h,t))
      } else_ {
        BooleanLiteral(true)
      }
    }

    (args, retType, body)
  }

  //as a precondition we assume the element is in the array
  val atID = FreshIdentifier("at")
  val atFunction: FunDef = mkFunDef(atID)("A"){ case Seq(aT) =>
    val args: Seq[ValDef] = Seq("l" :: T(list)(aT), "i" :: IntegerType)
    val retType: Type = aT
    val body: Seq[Variable] => Expr = { case Seq(l,i) => 
      if_ (i === E(BigInt(0))) {
        l.asInstOf(T(cons)(aT)).getField(head)
      } else_ {
        E(atID)(aT)(l.asInstOf(T(cons)(aT)).getField(tail),i - E(BigInt(1)))
      }
    }

    (args, retType, body)
  }

  //We would need i to be a natural number!!
  val dropID = FreshIdentifier("drop")
  val dropFunction: FunDef = mkFunDef(dropID)("A"){ case Seq(aT) =>
    val args: Seq[ValDef] = Seq("l" :: T(list)(aT), "i" :: IntegerType)
    val retType: Type = T(list)(aT)
    val body: Seq[Variable] => Expr = { case Seq(l,i) => 
      if_ (l.isInstOf(T(cons)(aT)) && i >= E(BigInt(0))) {
        if_ (i > E(BigInt(0))) {
          E(dropID)(aT)(l.asInstOf(T(cons)(aT)).getField(tail),i - E(BigInt(1)))
        } else_ {
          l
        }
      } else_ {
        T(nil)(aT)()
      }
    }

    (args, retType, body)
  }

  // returns the position of x in the array, -1 otherwise
  val indexOfID = FreshIdentifier("drop")
  val indexOfFunction: FunDef = mkFunDef(indexOfID)("A"){ case Seq(aT) =>
    val args: Seq[ValDef] = Seq("x" :: aT,"l" :: T(list)(aT))
    val retType: Type = IntegerType
    val body: Seq[Variable] => Expr = { case Seq(x,l) => 
      if_ (l.isInstOf(T(cons)(aT))) {
        if_ (x === l.asInstOf(T(cons)(aT)).getField(head)) {
          E(BigInt(0))
        } else_ {
          val t = l.asInstOf(T(cons)(aT)).getField(tail)
          E(BigInt(1)) + E(indexOfID)(aT)(x,t)
        }
      } else_ {
        E(BigInt(-1))
      }
    }

    (args, retType, body)
  }

  val drop = E(dropID)
  val indexOf = E(indexOfID)
  val at = E(atID)
  
}  

