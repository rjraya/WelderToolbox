import inox._
import inox.trees._
import inox.trees.dsl._
import welder._

object GaussProof {

  import Gauss._
  import Register._
  import theory._

  val gaussTheorem = {
    def property(n: Expr): Expr = {
      E(sumID)(n) === n * (n + E(BigInt(1))) / E(BigInt(2))
    }

    natInduct(property _, E(BigInt(0)), trivial)
  }

}
