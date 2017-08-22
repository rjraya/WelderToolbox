import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._
import welder._

object Tree {
  val tree = FreshIdentifier("Tree")
  val node = FreshIdentifier("Node")
  val leaf = FreshIdentifier("Leaf")

  val data = FreshIdentifier("data")
  val left = FreshIdentifier("left")
  val right = FreshIdentifier("right")

  val treeADT = mkSort(tree)("A")(Seq(node, leaf))
  val leafADT = mkConstructor(leaf)("A")(Some(tree))(_ => Seq())
  val nodeADT = mkConstructor(node)("A")(Some(tree)) { case Seq(aT) =>
    Seq(ValDef(data, aT), ValDef(left,T(tree)(aT)),ValDef(right, T(tree)(aT)))
  }


  val heightID = FreshIdentifier("h")
  val heightFunction: FunDef = mkFunDef(heightID)("A"){ case Seq(aT) =>
    val args: Seq[ValDef] = Seq("t" :: T(tree)(aT))
    val retType: Type = IntegerType
    val body: Seq[Variable] => Expr = { case Seq(t) =>
      if_ (t.isInstOf(T(node)(aT))) {
        val n = t.asInstOf(T(node)(aT))
        val lheight = E(heightID)(n.getField(left))
        val rheight = E(heightID)(n.getField(right))
        if_ (lheight > rheight){
          E(BigInt(1)) + lheight
        } else_ {
          E(BigInt(1)) + rheight
        }
      } else_ { // leaf
        E(BigInt(0))
      }
    }

    (args, retType, body)
  }


}
