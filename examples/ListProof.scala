import inox._
import inox.trees._
import inox.trees.dsl._
import welder._

object ListProof {

  import List._
  import Register._
  import theory._


  lazy val lengthLemma: Theorem = {
    def property(x: Expr) = {
      len(IntegerType)(x) >= E(BigInt(0))
    }
    induct(property _, "l" :: T(list)(IntegerType))
  }

}