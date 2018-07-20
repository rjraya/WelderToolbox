import inox._
import inox.trees.{forall => _, _}
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

  lazy val listTheorem1: Theorem = {
  	//itrev xs ys = rev xs @ ys
    println(T(nil)(IntegerType)())
  	def property(x: Expr) = {
      linearRev(IntegerType)(x,T(nil)(IntegerType)()) === rev(IntegerType)(x)
  	}

  	induct(property _, "l" :: T(list)(IntegerType))
  } 

  lazy val listTheorem: Theorem = {

  	def property(x: Expr) = {
      forall("y" :: T(list)(IntegerType)){ case (y) =>
      	linearRev(IntegerType)(x,y) === rev(IntegerType)(append(IntegerType)(x,y))
      }   
  	}

  	structuralInduction(property _, "x" :: T(list)(IntegerType)) { case (ihs, _) =>
  	  forallI("y" :: T(list)(IntegerType)){ case (y) =>
        val xi = ihs.expression 

        xi match{
          case C(`nil`) => truth
          case C(`cons`,h,t) => 
          	val lemma = forallE(ihs.hypothesis(t))(append(IntegerType)(T(cons)(IntegerType)(h,T(nil)(IntegerType)()),y))
          	println(lemma)
          	lemma
        }
      }  
    }
  } 


}