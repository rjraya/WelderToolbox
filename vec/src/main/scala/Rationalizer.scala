import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object Rationalizer{
  import Field._
  //assume third component is not zero
  val projectionID = FreshIdentifier("p")
  val projectionFunction = mkFunDef(projectionID)() { case Seq() => 
    val args: Seq[ValDef] = Seq("x" :: TupleType(Seq(F,F,F)))
    val retType: Type = TupleType(Seq(F,F))
    val body: Seq[Variable] => Expr = { case Seq(x) =>
      val u = x._1
      val v = x._2
      val w = x._3
      E(u ^/ (w ^^ E(BigInt(2))), v ^/ (w ^^ E(BigInt(3))))
    }
    (args, retType, body)
  }   

  /*val projectedAdditionID = FreshIdentifier("pplus")
  val projectedAdditionFunction = mkFunDef(projectedAdditionID)() { case Seq() => 
    val args: Seq[ValDef] = Seq("u" :: F,"v" :: F,"w" :: F)
    val retType: Type = TupleType(Seq(F,F))
    val body: Seq[Variable] => Expr = { case Seq(u,v,w) =>
      (u / (w ^^ E(BigInt(2))), v / (w ^^ E(BigInt(3))))
    }
    (args, retType, body)
  }   */

}