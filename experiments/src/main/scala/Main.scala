import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object Main {
  import List._
  import Register._
  import theory._


  def main(args: Array[String]): Unit = {
    /*val theorem = prove(
      forall("x" :: T(list)(IntegerType)){ case (x) =>
        len(IntegerType)(x) >= E(BigInt(0))
      }
    )
    println(theorem)*/

    lazy val firstLemma: Theorem = {
      def property(x: Expr) = {
        len(IntegerType)(x) >= E(BigInt(0))
      }
      induct(property _, "l" :: T(list)(IntegerType))
    }
    println(firstLemma)
    /*val k = Variable.fresh("k",T(cons)(IntegerType))
    val hk = k.asInstOf(T(cons)(IntegerType)).getField(head)
    val tk = k.asInstOf(T(cons)(IntegerType)).getField(tail)
    val or1 = !(len(IntegerType)(k) >= E(BigInt(0))) &&
      ( k === T(cons)(IntegerType)(hk,tk) ) ==> (len(IntegerType)(tk) >= E(BigInt(0)))
    val or2 = forall("x"::T(cons)(IntegerType)){ case (x) => len(IntegerType)(x) >= E(BigInt(0)) }

    val theorem2 = prove(or2 || or1)

    println(theorem2)*/
  }
}
