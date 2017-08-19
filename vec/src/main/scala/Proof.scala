import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object Proof{
  import Field._
  import Curve._
  import FieldProof._
  import Register._
  import theory._
  

  //Beware! We have to proof that the addition of curve points is on the curve
  /*val theorem: Theorem = prove(
    forall("p1" :: affine, "p2" :: affine, "a" :: F, "b" :: F){ case (p1,p2,a,b) =>
      {onCurve(p1,a,b) && onCurve(p2,a,b)} ==> onCurve(addCurve(p1,p2,a,b),a,b)
    }
  )*/

  //---------------------------Proof of commutativity-----------------------------------

  // If !onCurve(p1) || !onCurve(p2) || p1 = inf || p2 = inf then p1 + p2 = p2 + p1
  lazy val lemma1: Theorem = prove(
    forall("p1" :: affine, "p2" :: affine, "a" :: F, "b" :: F){ case (p1,p2,a,b) =>
      {!onCurve(p1,a,b) || !onCurve(p2,a,b) || p1.isInstOf(infinite) || p2.isInstOf(infinite)} ==> 
      {addCurve(p1,p2,a,b) === addCurve(p2,p1,a,b)}
    }
  )
 
  // If p1,p2 are finite and on curve and have equal first component then p1 + p2 = p2 + p1
  lazy val lemma2: Theorem = prove(
    forall("p1" :: affine, "p2" :: affine, "a" :: F, "b" :: F){ case (p1,p2,a,b) =>
      val x1 = p1.asInstOf(finite).getField(first)
      val x2 = p2.asInstOf(finite).getField(first)
      val hypothesis = p1.isInstOf(finite) && p2.isInstOf(finite) &&
                       onCurve(p1,a,b) && onCurve(p2,a,b) && (x1 === x2)
      hypothesis ==> {addCurve(p1,p2,a,b) === addCurve(p2,p1,a,b)}
    }
  )

  // If p1,p2 are finite and on curve and have different first component then p1 + p2 = p2 + p1
  /*lazy val theorem: Theorem = 
    forallI("p1" :: affine, "p2" :: affine, "a" :: F, "b" :: F){ case (p1,p2,a,b) =>
      val x1 = p1.asInstOf(finite).getField(first)
      val x2 = p2.asInstOf(finite).getField(first)
      val hypothesis = p1.isInstOf(finite) && p2.isInstOf(finite) &&
                       onCurve(p1,a,b) && onCurve(p2,a,b) && (x1 !== x2)
      implI(hypothesis){ case axioms =>
        val lambda = (y2 ^- y1) ^/ (x2 ^- x1) 
        val x3 = (lambda ^* lambda) ^- x1 ^- x2
        val y3 = (lambda ^* (x1 ^- x3)) ^- y1
        (y2 ^- y1) ^/ (x2 ^- x1) 
        y3 ==| |
        //addCurve(p1,p2,a,b) ==| axioms |
        //finite(x3,y3)
      }
      //{addCurve(p1,p2,a,b) === addCurve(p2,p1,a,b)}
    }*/
  
  //---------------------------Proof of neutral element-----------------------------------
  lazy val addNeutralElementLemma: Theorem = prove( 
    forall("p" :: affine, "a" :: F, "b" :: F){ case (p,a,b) =>
      onCurve(infinite(),a,b) &&
      {onCurve(p,a,b) ==> {addCurve(p,infinite(),a,b) === p && addCurve(infinite(),p,a,b) === p}}
    }
  )
  //---------------------------Proof of opposite element----------------------------------
  
  lazy val closedOppositeCurveLemma: Theorem = 
    implI(and(addOppositeElement,addNeutralElement,
              addAssociative,isDistributive)){ axioms =>
      val Seq(addOppositeElement,addNeutralElement,
              addAssociative,isDistributive) = andE(axioms) : Seq[Theorem]
      forallI("a"::F,"b"::F){ case (a,b) =>
        def property(p: Expr) = {
          onCurve(p,a,b) === onCurve(oppCurve(p),a,b)
        } 
        structuralInduction(property _,"p" :: affine) { case (ihs, goal) =>
          ihs.expression match{
            case C(`finitePoint`,x,y) =>
              onCurve(ihs.expression,a,b)                               ==| trivial |
              ((y ^* y) === {(x ^* x ^* x) ^+ (a ^* x) ^+ b})           ==| forallE(implE(oppositeInvolutionLemma)(g => axioms))(y ^* y) |
              (opp(opp(y ^* y)) === {(x ^* x ^* x) ^+ (a ^* x) ^+ b})   ==| forallE(implE(oppositeOfMultLemma)(g => axioms))(y,y)        |
              (opp(opp(y) ^* y) === {(x ^* x ^* x) ^+ (a ^* x) ^+ b})   ==| forallE(implE(oppositeOfMultLemma)(g => axioms))(opp(y),y)   |
              ((opp(y) ^* opp(y)) === {(x ^* x ^* x) ^+ (a ^* x) ^+ b}) ==| trivial |
              onCurve(oppCurve(ihs.expression),a,b)
            case C(`infinitePoint`) => truth
          }
        }
      }
    }
  
  lazy val addOppositeElementLemma: Theorem = 
    forallI("p"::affine, "a"::F,"b"::F){ case (p,a,b) =>

      val lemma1: Theorem = implI( and((!onCurve(p,a,b) || !onCurve(oppCurve(p),a,b)) &&
                                      (p.isInstOf(infinite) || oppCurve(p).isInstOf(infinite))) )
      { easyCases => prove(
          (addCurve(p,oppCurve(p),a,b) === infinite()) && 
          (addCurve(oppCurve(p),p,a,b) === infinite()), easyCases
        )
      }

      implI(and(addNeutralElement,addOppositeElement,addAssociative,
            multInverseElement,isDistributive,notCharacteristic2)){ fieldAxioms => 
        val Seq(addNeutralElement,addOppositeElement,addAssociative,
                multInverseElement,isDistributive,notCharacteristic2) = andE(fieldAxioms) : Seq[Theorem]

        val lemma2: Theorem = 
          implI( and(p.isInstOf(finite),oppCurve(p).isInstOf(finite), 
                     onCurve(p,a,b),onCurve(oppCurve(p),a,b)))
          { notEasyCases =>
            val Seq(pFinite,oppPFinite,onP,onOpp) = andE(notEasyCases) : Seq[Theorem]

            val x1 = p.asInstOf(finite).getField(first)
            val y1 = p.asInstOf(finite).getField(second)
            val x2 = oppCurve(p).asInstOf(finite).getField(first)
            val y2 = oppCurve(p).asInstOf(finite).getField(second)

            val unroll1 = prove(x1 === x2, notEasyCases)
            val unroll2 = prove(y2 === opp(y1), notEasyCases)

            val case1 = implI(!((y1 === y2) && (y1 !== z))){ hyp3 =>
              prove(
                (addCurve(p,oppCurve(p),a,b) === infinite()) && 
                (addCurve(oppCurve(p),p,a,b) === infinite()), 
                hyp3, pFinite,oppPFinite,onP,onOpp,unroll1
              ) 
            }
        
            val case2 = notI((y1 === y2) && (y1 !== z)){ case (hyp4,_) => 
              val Seq(eqLemma,nEqLemma) = andE(hyp4) : Seq[Theorem]
              val deriv = prove(y1 === opp(y1),unroll2,eqLemma) 
              val deriv1 = z              ==| forallE(addOppositeElement)(y1) | 
                          (y1 ^+ opp(y1)) ==| deriv                           | 
                          (y1 ^+ y1)
              val deriv2 = y1             ==| implE(forallE(doubleXZeroLemma)(y1))(g => 
                                                    andI(deriv1,addNeutralElement,addOppositeElement,addAssociative,
                                                    multInverseElement,isDistributive,notCharacteristic2)) | 
                           z
              andI(nEqLemma,deriv2)  
            }
            andI(case1,case2)
          }

          prove((addCurve(p,oppCurve(p),a,b) === infinite()) && 
                (addCurve(oppCurve(p),p,a,b) === infinite()), lemma1, lemma2)
        }        
      }
    
  //---------------------------Proof of associativity--------------------------------------

  /*val theorem: Theorem = prove(
    addAssociative && multAssociative ==>
    forall("a" :: F, "b" :: F){ case (a,b) => 
      forall("p1" :: affine, "p2" :: affine, "p3" :: affine){ case (p1,p2,p3) =>
        addCurve(p1,addCurve(p2,p3,a,b),a,b) === addCurve(addCurve(p1,p2,a,b),p3,a,b)
      }
    }
  )*/
}