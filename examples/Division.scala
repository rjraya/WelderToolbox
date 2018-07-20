import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object Division {

  val divID = FreshIdentifier("div")
  val divFunction = mkFunDef(divID)() {  _ =>
    val args: Seq[ValDef] = Seq("n" :: IntegerType)
    val retType: Type = IntegerType
    val body: Seq[Variable] => Expr = { case Seq(n) =>
      if_ (n === E(BigInt(0))) {
        E(BigInt(0))
      } else_ {
        if_ (n === E(BigInt(1))){
          E(BigInt(0))
        } else_ {
          E(divID)(n - E(BigInt(2))) + E(BigInt(1))
        }        
      }
    }
    (args, retType, body)
  }

}