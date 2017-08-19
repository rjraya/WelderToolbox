import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object ReduceProof{
  import Reduce._
  import Field._
  import FieldProof._
  import SparsePolynomial._
  import Register._
  import theory._

  val thetaevaluationTheorem = implI(and(multNeutralElement,multCommutative,isDistributive)) { axioms =>
    val Seq(multNeutralElement,multCommutative, isDistributive) = andE(axioms): Seq[Theorem]

    val lemma2 =
      (x0 ^* ((x0 ^^ E(BigInt(2))) ^+ A)) ==|
        andI(forallE(isDistributive)(x0,x0 ^^ E(BigInt(2)),A),
          forallE(multCommutative)(x0,A),
          forallE(multCommutative)(x0,x0 ^^ E(BigInt(2)))) |
      ((x0 ^^ E(BigInt(3))) ^+ (A ^* x0))

    evalh(theta, vals) ==| forallE(multNeutralElement)(x0 ^^ E(BigInt(2))) |
      ((
        (x0 ^^ E(BigInt(1))) ^*
          (((x0 ^^ E(BigInt(2))) ^* one) ^+ A) ^+
          B)) ==| forallE(multNeutralElement)(x0) |
      ((
        x0 ^*
          (((x0 ^^ E(BigInt(2))) ^* one) ^+ A) ^+
          B)) ==| andI(axioms,lemma2) |
      ((
        ((x0 ^^ E(BigInt(3))) ^+ (A ^* x0)) ^+
          B))

  }





}
