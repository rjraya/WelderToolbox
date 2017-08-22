import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object Gauss {

  val sumID = FreshIdentifier("sum")
  val sumFunction = mkFunDef(sumID)() {  _ =>
    val args: Seq[ValDef] = Seq("n" :: IntegerType)
    val retType: Type = IntegerType
    val body: Seq[Variable] => Expr = { case Seq(n) =>
      if_ (n === E(BigInt(0))) {
        E(BigInt(0))
      } else_ {
        E(sumID)(n - E(BigInt(1))) + n
      }
    }

    (args, retType, body)
  }

}