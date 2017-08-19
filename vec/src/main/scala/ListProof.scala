import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object ListProof{
  import List._
  import Field._
  import Register._
  import theory._

  // can we generalize the type?
  // i,j >= 0 ==> drop(i+j,l) = drop(i,drop(j,l))
  lazy val rephrasedropLemma: Theorem =
    forallI("i" :: IntegerType){ case (i) => 
    def property(j: Expr) = {
      (i >= E(BigInt(0)) && j >= E(BigInt(0))) ==> 
      {forall("l" :: T(list)(F)){ case (l) =>       
        (drop(F)(l,i+j) === drop(F)(drop(F)(l,j),i))
      }}    
    } 
    
    naturalInduction(property _, E(BigInt(0)), trivial) { case (ihs, goal) =>
      val n = ihs.variable
      implI(and(i >= E(BigInt(0)),n >= E(BigInt(0)))){ axioms => 
        forallI("l" :: T(list)(F)){ case (l) => 
          val conslemma: Theorem = implI(l.isInstOf(T(cons)(F))) { conshyp =>
            val t = l.asInstOf(T(cons)(F)).getField(tail)
            drop(F)(l,i+(n+E(BigInt(1)))) ==| andI(axioms,conshyp) | 
            drop(F)(t,i + n)              ==| forallE(implE(ihs.propertyForVar)(g => axioms))(t) |
            drop(F)(drop(F)(t,n),i)       ==| andI(axioms,conshyp) | 
            drop(F)(drop(F)(l,n + E(BigInt(1))),i)
          }
          val nillemma: Theorem = implI(l.isInstOf(T(nil)(F))){ nilhyp => nilhyp}
          andI(conslemma,nillemma)
        }
      }  
    }
  }

  //To do: put together the two lemmas
  // i,j >= 0 ==> drop(i+j,l) === drop(i,drop(l,j))
  lazy val dropLemma: Theorem = prove(
    forall("i" :: IntegerType, "j" :: IntegerType, "l" :: T(list)(F)){ case (i,j,l) =>
      (i >= E(BigInt(0)) && j >= E(BigInt(0))) ==> (drop(F)(l,i+j) === drop(F)(drop(F)(l,j),i))
    },rephrasedropLemma
  )

  lazy val firstLemma: Theorem = {
    def property(l: Expr) = {
      forall("i" :: IntegerType, "j" :: IntegerType){ case (i,j) =>
        (i >= E(BigInt(0)) && j >= E(BigInt(0))) ==> (drop(F)(l,i+j) === drop(F)(drop(F)(l,j),i))
      }
    }
    induct(property _, "l" :: T(list)(F))
  }

}