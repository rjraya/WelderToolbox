import inox._
import inox.trees._
import inox.trees.dsl._
import welder._

object DivisionProof {

  import Division._
  import Register._
  import theory._

  val divisionTheorem = {
    def property(n: Expr): Expr = {
      E(divID)(n) === (n / E(BigInt(2))) 
    }

    natInduct(property _, E(BigInt(0)), trivial)
  }

}
