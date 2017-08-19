import inox.trees.{forall => _, _}
import inox.trees.dsl._

object SparseProof{
  import Field._
  import FieldProof._
  import SparsePolynomial._
  import List._
  import ListProof._
  import Register._
  import theory._

  lazy val normalityLemma: Theorem = {
    def property(x: Expr) = {
      shfnormp(x) ==> shfp(x)
    }
    structuralInduction(property _, "x" :: shf) { case (ihs,_) =>
      val xi = ihs.expression 
      implI(shfnormp(xi)){ normal =>
      xi match{
        case C(`constshfID`, _) => truth
        case C(`POP_ID`,i,p) => andI(ihs.hypothesis(p),normal)
        case C(`POW_ID`,p,i,q) => andI(ihs.hypothesis(p),ihs.hypothesis(q),normal)
      }
    }}
  }

  // Theorems for the count function.
  // shfCount(p) > 0
  lazy val countLemma: Theorem = {
    def property(p: Expr) = {
      shfCount(p) > E(BigInt(0))
    }
    structuralInduction(property _, "p" :: shf) { case (ihs, _) =>
      val pi = ihs.expression 
      pi match{
        case C(`constshfID`, _) => trivial
        case C(`POP_ID`,i,p) => ihs.hypothesis(p)
        case C(`POW_ID`,p,_,q) => andI(ihs.hypothesis(p),ihs.hypothesis(q))
      }
    }
  }

  //theorems form the shnf definition
  // normal POW i p q => p,q are normal
  // horner x && x != pow,pop => x = const
  // integer x => normal x

  // normpop(i,p) is normal
  lazy val normpop1Lemma: Theorem = prove(
    forall("i" :: IntegerType, "p" :: shf){ case (i,p) => 
      (i >= E(BigInt(0)) && shfp(p) && shfnormp(p)) ==> shfnormp(pop(i,p))
    }
  )
  // evalh (normpop(i,p),l) = evalh(POP(i,p),l)
  lazy val normpop2Lemma: Theorem = prove(
    forall("i" :: IntegerType, "p" :: shf, "l" :: T(list)(F)){ case (i,p,l) => 
      ((i > E(BigInt(0))) && shfp(p)) ==> (evalh(pop(i,p),l) === evalh(POP(i,p),l))

    }, dropLemma
  )

  lazy val normpop3Lemma: Theorem = prove(
      forall("i" :: IntegerType, "p" :: shf){ case (i,p) =>
        shfCount(pop(i,p)) <= shfCount(POP(i,p))
      }
    )

  // normal p,q && i !== 0 => normal normpow(i,p,q)
  lazy val normpow1Lemma: Theorem = prove(
    forall("p" :: shf, "i" :: IntegerType, "q" :: shf){ case (p,i,q) => 
      val phyp = shfp(p) && shfnormp(p)
      val qhyp = shfp(q) && shfnormp(q)
      (i > E(BigInt(0)) && phyp && qhyp) ==> shfnormp(pow(p,i,q))
    }
  )

  // if p = 0 then evalh(pow(i,p,q)) = evalh(POW(i,p,q))
  lazy val normpow21Lemma: Theorem = 
    forallI("i" :: IntegerType, "p" :: shf, "q" :: shf, "l" :: T(list)(F)){ case (i,p,q,l) => 
      val c = p.asInstOf(constshf).getField(fc)
      implI(and(shfp(q),shfnormp(q),
                addOppositeElement,addNeutralElement,addAssociative,isDistributive,
                p.isInstOf(constshf),c === z)){ axioms =>
        val Seq(qpol,qnormal,addO,addN,addA,isDistr,isConst,isZero) = andE(axioms): Seq[Theorem]
        val h = l.asInstOf(T(cons)(F)).getField(head)
        val t = l.asInstOf(T(cons)(F)).getField(tail)
        val lemma1 = implE(forallE(normpop1Lemma)(E(BigInt(1)),q))(_ => andI(qpol,qnormal))
        val lemma2 = forallE(implE(zeroDivisorLemma)(_ => andI(addO,addN,addA,isDistr)))(h ^^ i)
        val lemma3 = forallE(addN)(evalh(q, t))
        prove(evalh(pow(p,i,q),l) === evalh(POW(p,i,q),l),isConst, isZero,lemma1,lemma3,lemma2)
      }  
    }


  // if p = POW(j,r,0), consp l => evalh(pow(j,r,0),l) = evalh(POW(j,r,0),l)
  lazy val normpow22powLemma: Theorem =
    forallI("i" :: IntegerType, "p" :: shf, "q" :: shf, "l" :: T(list)(F)){ case (i,p,q,l) =>
      val h = l.asInstOf(T(cons)(F)).getField(head) 
      val t = l.asInstOf(T(cons)(F)).getField(tail)
      val r = p.asInstOf(POW).getField(pshf)
      val j = p.asInstOf(POW).getField(vi)      
      val s = p.asInstOf(POW).getField(qshf)
      val c = s.asInstOf(constshf).getField(fc)
      implI(and(i > E(BigInt(0)),shfp(p), addNeutralElement, multAssociative,multNeutralElement,
                p.isInstOf(POW),s.isInstOf(constshf), c === z)){ axioms =>
        val Seq(iNat,ppol,addN,mulA,mulN,powp,sconst,szero) = andE(axioms): Seq[Theorem]
        val lemma0 = prove(
          forall("p" :: shf){ case (p) =>
            (p.isInstOf(POW) && shfp(p)) ==> (p.asInstOf(POW).getField(vi) >= E(BigInt(0)))
          }
        )
        val lemma1 = implE(forallE(exp2Theorem)(h,i,j))(_ => andI(iNat,mulA,mulN,ppol,powp,lemma0))
        val lemma2 = forallE(mulA)(h ^^ i, h ^^ j, evalh(r,l))
        val lemma3 = forallE(addN)((h ^^ j) ^* evalh(r,l))
        prove(evalh(pow(p,i,q),l) === evalh(POW(p,i,q),l),lemma1,lemma2,lemma3,
              powp,sconst,szero)
      }
    } 
    // normal(p,q) && i != 0 => evalh(normpow(i,p,q),l) = evalh(POW(i,p,q),l)
  lazy val normpow2Theorem: Theorem =
    forallI("i" :: IntegerType, "p" :: shf, "q" :: shf, "l" :: T(list)(F)){ case (i,p,q,l) =>
      implI(and(i > E(BigInt(0)),shfp(p),shfp(q),shfnormp(q),
                addOppositeElement,addNeutralElement,addAssociative,
                isDistributive,multAssociative,multNeutralElement)){ axioms =>
      val Seq(iNat,shfpp,shpq,shfnormpq,addOp,
              addNeu,addAssoc,isDistr,multAssoc,multNeu): Seq[Theorem] = andE(axioms)
      val lemma1 = forallE(normpow22powLemma)(i,p,q,l)
      val lemma2 = forallE(normpow21Lemma)(i,p,q,l)
      val s = p.asInstOf(POW).getField(qshf)
      val c = s.asInstOf(constshf).getField(fc)
      val assumption = p.isInstOf(POW) && s.isInstOf(constshf) && c === z
      val assump = andI(iNat,shfpp,addNeu,multAssoc,multNeu)
      val powCase = implI(assumption) { assumpt =>
        implE(lemma1)(_ => andI(assump, assumpt))
      }
      val c2 = p.asInstOf(constshf).getField(fc)
      val assump2 = andI(shpq,shfnormpq,addOp,addNeu,addAssoc,isDistr)
      val zeroCase = implI(p.isInstOf(constshf) && c2 === z) { assumpt =>
        implE(lemma2)(_ => andI(assump2,assumpt))
      }
      evalh(pow(p,i,q),l) ==| andI(axioms,powCase,zeroCase) | evalh(POW(p,i,q),l)
      }
    }

  // theorems from the normvar definition
  // member x vars => shnfp norm-var(x,vars)
  // distinct-symbols vars && all-integers vals && len vars <= len vals && member(x,vars)
  //   evalh(normvar(x,vars) vals) = evalp(x,vars zip vals)

  // shnf(x,y) => shnf(normadd(x,y))
  lazy val normAddLemma1: Theorem = {
    def property(n: Expr): Expr = {
      forall("x" :: shf, "y" :: shf){ case (x,y) => 
        (n === shfCount(x) + shfCount(y) && 
         shfp(x) && shfp(y) && 
         shfnormp(x) && shfnormp(y)) ==> shfnormp(normadd(x,y))
      }
    }
    naturalInduction(property _, E(BigInt(0)),(_:Goal).by(countLemma)) { case (ihs, _) =>
      val n = ihs.variable
      val next = n + E(BigInt(1))
      def strongHypFun(a: Expr, b: Expr,lemma: Theorem): Theorem = {
        val m = shfCount(a) + shfCount(b)
        forallE(implE(forallE(ihs.propertyForLessOrEqualToVar)(m))( _ =>
          lemma))(a,b)
      }
      def property1(x: Expr): Expr = 
        forall("y" :: shf){ case (y) => 
          (next === shfCount(x) + shfCount(y) && 
         shfp(x) && shfp(y) && 
         shfnormp(x) && shfnormp(y)) ==> shfnormp(normadd(x,y))
        }
        structuralInduction(property1 _, "x" :: shf) { case (ihs1, _) =>
          val xi = ihs1.expression
          def property2(y: Expr): Expr = {
            (next === shfCount(xi) + shfCount(y) && 
             shfp(xi) && shfp(y) && 
             shfnormp(xi) && shfnormp(y)) ==> shfnormp(normadd(xi,y))
          }
          xi match{
            case C(`constshfID`, c) =>          
              structuralInduction(property2 _, "y" :: shf) { case (ihs2, _) =>
                val yi = ihs2.expression
                implI(next === shfCount(xi) + shfCount(yi) &&
                       shfp(xi) && shfp(yi) && 
                       shfnormp(xi) && shfnormp(yi)){ case axioms =>
                yi match{
                  case C(`constshfID`, _) => truth
                  case C(`POP_ID`,_,p) =>
                    val lemma = andI(axioms,forallE(countLemma)(p))
                    strongHypFun(xi,p,lemma)
                  case C(`POW_ID`,p,i,q) => 
                    val lemma = andI(axioms,forallE(countLemma)(p),forallE(countLemma)(q))
                    strongHypFun(xi,q,lemma)
                }
              }}
            case C(`POP_ID`,i,p) => 
              structuralInduction(property2 _, "p" :: shf) { case (ihs2, _) =>
                val yi = ihs2.expression
                implI(next === shfCount(xi) + shfCount(yi) &&
                       shfp(xi) && shfp(yi) && 
                       shfnormp(xi) && shfnormp(yi)){ axioms =>
                yi match {
                  case C(`constshfID`, _) =>
                    val lemma = andI(axioms,forallE(countLemma)(p))
                    strongHypFun(p,yi,lemma)
                  case C(`POP_ID`,j,q) => 
                    val lemma = andI(axioms,forallE(countLemma)(p),forallE(countLemma)(q))
                    val strongHyp1 = strongHypFun(p,q,lemma) 
                    val strongHyp2 = strongHypFun(POP(i-j,p),q,lemma) 
                    val strongHyp3 = strongHypFun(POP(j-i,q),p,lemma)  
                    andI(strongHyp1,strongHyp2,strongHyp3)
                  case C(`POW_ID`,q,_,r) =>
                    val lemma = andI(axioms,forallE(countLemma)(r),forallE(countLemma)(p),forallE(countLemma)(q))
                    val strongHyp1 = strongHypFun(r,p,lemma) 
                    val strongHyp2 = strongHypFun(r,POP(i-E(BigInt(1)),p),lemma) 
                    andI(strongHyp1,strongHyp2)
                }
              }}  
            case C(`POW_ID`,p,i,q) => 
              structuralInduction(property2 _, "p" :: shf) { case (ihs2, _) =>
                val yi = ihs2.expression
                implI(and(next === shfCount(xi) + shfCount(yi),
                       shfp(xi),shfp(yi),shfnormp(xi),shfnormp(yi))){ axioms =>
                val Seq(ind,shpx,shpy,shpnormx,shpnormy): Seq[Theorem] = andE(axioms)
                yi match{
                  case C(`constshfID`,_) =>
                    strongHypFun(q,yi,andI(axioms,forallE(countLemma)(p),forallE(countLemma)(q)))
                  case C(`POP_ID`,j,r) => 
                    val lemma = andI(axioms,forallE(countLemma)(q),forallE(countLemma)(r),forallE(countLemma)(p))
                    val strongHyp1 = strongHypFun(q,r,lemma) 
                    val strongHyp2 = strongHypFun(q,POP(j-E(BigInt(1)),r),lemma) 
                    andI(strongHyp1,strongHyp2)
                  case C(`POW_ID`,r,j,s) => 
                    val Seq(countq,countr,countp,counts): Seq[Theorem] =
                        Seq(forallE(countLemma)(q),forallE(countLemma)(r),
                             forallE(countLemma)(p),forallE(countLemma)(s))
                    val lemma = andI(countq, counts, countp,countr,ind)
                    val strongHyp1 = strongHypFun(p,r,lemma)
                    val norm1 = implE(strongHyp1)(_ => axioms)
                    val shp1 = implE(forallE(normalityLemma)(normadd(p,r)))(_ => norm1)
                    val strongHyp2 = strongHypFun(q,s,lemma)
                    val norm2 = implE(strongHyp2)(_ => axioms)
                    val shp2 = implE(forallE(normalityLemma)(normadd(q,s)))(_ => norm2)
                    val strongHyp3 = strongHypFun(POW(p,i-j,constshf(z)),r,lemma)
                    val strongHyp4 = strongHypFun(POW(r,j-i,constshf(z)),p,lemma)
                    val strongHyp5 = strongHypFun(s,q,lemma)
                    val caseEq =
                      implE(forallE(normpow1Lemma)(normadd(p,r),i,normadd(q,s)))(_ =>
                        andI(axioms, norm1,shp1, norm2, shp2))
                    val caseGreater = implI(i > j) { gt =>
                      val norm3 = implE(strongHyp3)(_ => andI(axioms,gt))
                      val shp3 = implE(forallE(normalityLemma)(normadd(POW(p,i-j,constshf(z)),r)))(_ => norm3)
                      implE(forallE(normpow1Lemma)(normadd(POW(p, i - j, constshf(z)), r), j, normadd(q, s)))(_ =>
                        andI(axioms, norm2, shp2,norm3, shp3))
                    }
                    val caseLess = implI(i < j) { lt =>
                      val norm4 = implE(strongHyp4)(_ => andI(axioms,lt))
                      val shp4 = implE(forallE(normalityLemma)(normadd(POW(r,j-i,constshf(z)),p)))(_ => norm4)
                      val norm5 = implE(strongHyp5)(_ => andI(axioms,lt))
                      val shp5 = implE(forallE(normalityLemma)(normadd(s,q)))(_ => norm5)
                      implE(forallE(normpow1Lemma)(normadd(POW(r, j - i, constshf(z)), p), i, normadd(s, q)))(_ =>
                        andI(axioms,norm4,shp4,norm5,shp5))
                    }
                    andI(caseEq,caseGreater,caseLess)
                }
              }}
            }
          }
        }  
      }
  // shnf(x,y) => shnf(normadd(x,y))
  lazy val normAddTheorem1: Theorem = 
    forallI("x" :: shf, "y" :: shf){ case (x,y) => 
      val sum = shfCount(x) + shfCount(y)  
      val proposition = 
        (shfp(x) && shfp(y) && shfnormp(x) && shfnormp(y)) ==> 
          shfnormp(normadd(x,y))    
      val proof = 
        implE(forallE(normAddLemma1)(sum))(
          _ => andI(forallE(countLemma)(x),forallE(countLemma)(y)))
      prove(proposition, proof)
    }

  // evalh(normadd(x,y),l) = evalh(x,l) + evalh(y,l)
  lazy val normAddLemma2: Theorem = {
    implI(and(addCommutative,addAssociative,addNeutralElement,addOppositeElement,
              multAssociative, multNeutralElement,isDistributive)){ addMultAxioms =>
    val Seq(addC,addAssoc,addN,addO,multA,multN,isDistr): Seq[Theorem] = andE(addMultAxioms) 
    def property(n: Expr): Expr = {
      forall("x" :: shf, "y" :: shf,"l" :: T(list)(F)){ case (x,y,l) => 
        (n === (shfCount(x) + shfCount(y)) && shfp(x) && shfp(y) && shfnormp(x) && shfnormp(y)) ==>
          (evalh(normadd(x,y),l) === (evalh(x,l) ^+ evalh(y,l)))
      }
    }
    naturalInduction(property _, E(BigInt(0)),(_:Goal).by(countLemma)) { case (ihs, goal) =>
      val n = ihs.variable
      val next = n + E(BigInt(1))
      def strongHypFun(a: Expr, b: Expr,axioms: Theorem,l: Expr): Theorem = {
        val m = shfCount(a) + shfCount(b)
        implE(forallE(implE(forallE(ihs.propertyForLessOrEqualToVar)(m))(g => 
          andI(axioms)))(a,b,l))(g => axioms)
      }
      def property1(x: Expr): Expr = 
        forall("y" :: shf,"l" :: T(list)(F)){ case (y,l) => 
          (next === (shfCount(x) + shfCount(y)) && shfp(x) && shfp(y) && shfnormp(x) && shfnormp(y)) ==>
            (evalh(normadd(x,y),l) === (evalh(x,l) ^+ evalh(y,l)))
        }
        structuralInduction(property1 _, "x" :: shf) { case (ihs1, _) =>
          val xi = ihs1.expression
          def property2(y: Expr): Expr = {
            forall("l" :: T(list)(F)){ case (l) =>
              (next === (shfCount(xi) + shfCount(y)) && shfp(xi) && shfp(y) && shfnormp(xi) && shfnormp(y)) ==> 
                (evalh(normadd(xi,y),l) === (evalh(xi,l) ^+ evalh(y,l)))
            }  
          }
          xi match{
            case C(`constshfID`, _) =>
              structuralInduction(property2 _, "y" :: shf) { case (ihs2, _) =>
                val yi = ihs2.expression
                forallI("l" :: T(list)(F)){ case (l) => 
                implI(next === (shfCount(xi) + shfCount(yi)) && shfp(xi) && shfp(yi) && shfnormp(xi) && shfnormp(yi)){ axioms =>
                yi match{
                  case C(`constshfID`, _) => truth
                  case C(`POP_ID`,i,p) => 
                    val hyp = forallE(countLemma)(p)
                    strongHypFun(xi,p,andI(axioms,hyp),drop(F)(l,i))
                  case C(`POW_ID`,p,i,q) => 
                    val hyp = andI(forallE(countLemma)(p),forallE(countLemma)(q))
                    val nilCase: Theorem = implI(l.isInstOf(T(nil)(F))){ isNil =>
                      val lemma = strongHypFun(xi,q,andI(axioms,hyp),l)
                      evalh(normadd(xi,yi),l)    ==| andI(isNil,lemma) |
                      (evalh(xi,l) ^+ evalh(q,l))
                    }
                    val consCase: Theorem = implI(l.isInstOf(T(cons)(F))){ isCons =>
                      val n = l.asInstOf(T(cons)(F)).getField(head)
                      val t = l.asInstOf(T(cons)(F)).getField(tail)
                      val lemma = strongHypFun(xi,q,andI(axioms,hyp),t)
                      val lemma2 = forallE(addAssoc)((n ^^ i) ^* evalh(p,l),evalh(xi,t),evalh(q,t))
                      val lemma3 = forallE(addC)((n ^^ i) ^* evalh(p,l),evalh(xi,t))
                      val lemma4 = forallE(addAssoc)(evalh(xi,t),(n ^^ i) ^* evalh(p,l),evalh(q,t))
                      evalh(normadd(xi,yi),l) ==| andI(isCons,lemma,lemma2,lemma3,lemma4) |
                      (evalh(xi,t) ^+ (((n ^^ i) ^* evalh(p,l)) ^+ evalh(q,t)))
                    }
                    andI(nilCase,consCase)
                }
              }}}
            case C(`POP_ID`,i,p) => 
              structuralInduction(property2 _, "p" :: shf) { case (ihs2, _) =>
                val yi = ihs2.expression
                forallI("l" :: T(list)(F)){ case (l) => 
                implI(next === (shfCount(xi) + shfCount(yi)) && shfp(xi) && shfp(yi) && shfnormp(xi) && shfnormp(yi)){ case axioms => 
                yi match {
                  case C(`constshfID`, _) =>
                    val hyp = forallE(countLemma)(p)
                    val lemma = strongHypFun(yi,p,andI(axioms,hyp),drop(F)(l,i))
                    val lemma2 = forallE(addC)(evalh(yi,drop(F)(l,i)),evalh(xi,l))
                    andI(lemma,lemma2)
                  case C(`POP_ID`,j,q) => 
                    val hyp = andI(forallE(countLemma)(p),forallE(countLemma)(q))
                    val iEqj: Theorem = implI(i === j){ ieqj =>
                      val lemma1 = forallE(normalityLemma)(normadd(p,q))
                      val lemma2 = forallE(normAddTheorem1)(p,q)
                      val lemma3 = implE(forallE(normpop2Lemma)(i,normadd(p,q),l))(g => andI(axioms,lemma1,lemma2))
                      val lemma4 = strongHypFun(p,q,andI(axioms,hyp),drop(F)(l,i))
                      prove(evalh(normadd(xi,yi),l) === (evalh(xi,l) ^+ evalh(yi,l)),lemma3,lemma4,ieqj)
                    }
                    val iGreaterThanJ: Theorem = implI(i > j){ igtj =>
                      val lemma1 = forallE(normalityLemma)(normadd(POP(i-j,p),q))
                      val lemma2 = forallE(normAddTheorem1)(POP(i-j,p),q)
                      val lemma3 = implE(forallE(normpop2Lemma)(j,normadd(POP(i-j,p),q),l))(g => andI(axioms,lemma1,lemma2,igtj))
                      val lemma4 = strongHypFun(POP(i-j,p),q,andI(axioms,hyp,igtj),drop(F)(l,j))
                      val lemma5 = implE(forallE(dropLemma)(i-j,j,l))(g => andI(axioms,igtj))
                      prove(evalh(normadd(xi,yi),l) === (evalh(xi,l) ^+ evalh(yi,l)),lemma3,lemma4,lemma5,igtj)
                    }
                    val iLessThanJ: Theorem = implI(i < j){ iltj =>
                      val lemma1 = forallE(normalityLemma)(normadd(POP(j-i,q),p))
                      val lemma2 = forallE(normAddTheorem1)(POP(j-i,q),p)
                      val lemma3 = implE(forallE(normpop2Lemma)(i,normadd(POP(j-i,q),p),l))(g => andI(axioms,lemma1,lemma2,iltj))
                      val lemma4 = strongHypFun(POP(j-i,q),p,andI(axioms,hyp,iltj),drop(F)(l,i))
                      val lemma5 = implE(forallE(dropLemma)(j-i,i,l))(g => andI(axioms,iltj))
                      val lemma6 = forallE(addC)(evalh(q,drop(F)(l,j)),evalh(p,drop(F)(l,i)))
                      prove(evalh(normadd(xi,yi),l) === (evalh(xi,l) ^+ evalh(yi,l)),lemma3,lemma4,lemma5,lemma6,iltj)
                    }
                    andI(iEqj,iGreaterThanJ,iLessThanJ)
                  case C(`POW_ID`,q,j,r) => 
                    val hyp = andI(forallE(countLemma)(q),forallE(countLemma)(p),forallE(countLemma)(r))
                    val nilCase: Theorem = implI(l.isInstOf(T(nil)(F))){ isNil =>
                      val lemma3 = forallE(addC)(evalh(r,l),evalh(p,l))
                      val oneCase: Theorem = implI(i === E(BigInt(1))){ isOne =>
                        val lemma1 = strongHypFun(r,p,andI(axioms,hyp,isOne),l)
                        evalh(normadd(xi,yi),l)    ==| andI(isOne,isNil,lemma1,lemma3) |
                        (evalh(xi,l) ^+ evalh(yi,l))    
                      }
                      val notOneCase: Theorem = implI(i > E(BigInt(1))){ notOne =>
                        val lemma2 = strongHypFun(r,POP(i-E(BigInt(1)),p),andI(axioms,hyp,notOne),l)
                        evalh(normadd(xi,yi),l)      ==| andI(notOne,isNil,lemma2,lemma3) |
                        (evalh(xi,l) ^+ evalh(yi,l))              
                      }
                      prove(evalh(normadd(xi,yi),l) === (evalh(xi,l) ^+ evalh(yi,l)),oneCase,notOneCase,isNil,axioms)
                    }

                    val consCase: Theorem = implI(l.isInstOf(T(cons)(F))){ isCons =>
                      val n = l.asInstOf(T(cons)(F)).getField(head)
                      val t = l.asInstOf(T(cons)(F)).getField(tail)
                      val commute1 = forallE(addC)(evalh(p,drop(F)(l,i)),(n^^j) ^* evalh(q,l))
                      val commute2 = forallE(addC)(evalh(r,t),evalh(p,drop(F)(l,i)))
                      val assoc1 = forallE(addAssoc)((n^^j) ^* evalh(q,l),evalh(p,drop(F)(l,i)),evalh(r,t))
                      val assoc2 = forallE(addAssoc)(evalh(p,drop(F)(l,i)),(n^^j) ^* evalh(q,l),evalh(r,t))
                      val deduct = 
                        (evalh(xi,l) ^+ evalh(yi,l)) ==| andI(isCons,assoc2,commute1,assoc1,commute2) | 
                        (((n^^j) ^* evalh(q,l)) ^+ (evalh(r,t) ^+ evalh(p,drop(F)(l,i))))

                      val oneCase: Theorem = implI(i === E(BigInt(1))){ isOne =>
                        val lemma1 = strongHypFun(r,p,andI(axioms,hyp),t)
                        evalh(normadd(xi,yi),l)  ==| andI(isOne,isCons,lemma1,deduct) |
                        (evalh(xi,l) ^+ evalh(yi,l))
                      }
                      val notOneCase: Theorem = implI(i > E(BigInt(1))){ notOne =>
                        val lemma2 = strongHypFun(r,POP(i-E(BigInt(1)),p),andI(axioms,hyp,notOne),t)
                        evalh(normadd(xi,yi),l) ==| andI(notOne,isCons,lemma2,deduct) |
                        (evalh(xi,l) ^+ evalh(yi,l))
                      }
                      prove(evalh(normadd(xi,yi),l) === (evalh(xi,l) ^+ evalh(yi,l)),oneCase,notOneCase,isCons,axioms)
                    }
                    andI(nilCase,consCase)
                  } 
              }}}
            case C(`POW_ID`,p,i,q) => 
              structuralInduction(property2 _, "p" :: shf) { case (ihs2, _) =>
                val yi = ihs2.expression
                forallI("l" :: T(list)(F)){ case (l) => 
                implI(next === (shfCount(xi) + shfCount(yi)) && shfp(xi) && shfp(yi) && shfnormp(xi) && shfnormp(yi)){ case axioms => 
                yi match{
                  case C(`constshfID`, c) => 
                    val hyp = andI(forallE(countLemma)(p),forallE(countLemma)(q))
                    val commute = forallE(addC)(evalh(yi,l),evalh(xi,l))
                    val nilCase: Theorem = implI(l.isInstOf(T(nil)(F))){ isNil =>
                      val lemma = strongHypFun(yi,q,andI(axioms,hyp),l)
                      evalh(normadd(xi,yi),l)    ==| andI(isNil,lemma,commute) |
                      (evalh(xi,l) ^+ evalh(yi,l)) 
                    }
                    val consCase: Theorem = implI(l.isInstOf(T(cons)(F))){ isCons =>
                      val n = l.asInstOf(T(cons)(F)).getField(head)
                      val t = l.asInstOf(T(cons)(F)).getField(tail)
                      val lemma = strongHypFun(yi,q,andI(axioms,hyp),t)
                      val lemma2 = forallE(addAssoc)((n ^^ i) ^* evalh(p,l),evalh(yi,t),evalh(q,t))
                      val lemma3 = forallE(addC)((n ^^ i) ^* evalh(p,l),evalh(yi,t))
                      val lemma4 = forallE(addAssoc)(evalh(yi,t),(n ^^ i) ^* evalh(p,l),evalh(q,t))
                      evalh(normadd(xi,yi),l) ==| andI(isCons,lemma,lemma2,lemma3,lemma4,commute) |
                      (evalh(xi,l) ^+ evalh(yi,l)) 
                    }
                    andI(nilCase,consCase)
                  case C(`POP_ID`,j,r) => 
                    val hyp = andI(forallE(countLemma)(p),forallE(countLemma)(q),forallE(countLemma)(r))
                    val commute = forallE(addC)(evalh(yi,l),evalh(xi,l))
                    val nilCase: Theorem = implI(l.isInstOf(T(nil)(F))){ isNil =>
                      val lemma3 = forallE(addC)(evalh(r,l),evalh(p,l))
                      val oneCase: Theorem = implI(j === E(BigInt(1))){ isOne =>
                        val lemma1 = strongHypFun(q,r,andI(axioms,hyp,isOne),l)
                        evalh(normadd(xi,yi),l)    ==| andI(isOne,isNil,lemma1,lemma3,commute) |
                        (evalh(xi,l) ^+ evalh(yi,l))    
                      }
                      val notOneCase: Theorem = implI(j > E(BigInt(1))){ notOne =>
                        val lemma2 = strongHypFun(q,POP(j-E(BigInt(1)),r),andI(axioms,hyp,notOne),l)
                        evalh(normadd(xi,yi),l)      ==| andI(notOne,isNil,lemma2,lemma3,commute) |
                        (evalh(xi,l) ^+ evalh(yi,l))              
                      }
                      andI(oneCase,notOneCase)
                    }
                    val consCase: Theorem = implI(l.isInstOf(T(cons)(F))){ isCons =>
                      val n = l.asInstOf(T(cons)(F)).getField(head)
                      val t = l.asInstOf(T(cons)(F)).getField(tail)
                      val commute1 = forallE(addC)(evalh(r,drop(F)(l,j)),(n^^i) ^* evalh(p,l))
                      val commute2 = forallE(addC)(evalh(q,t),evalh(r,drop(F)(l,j)))
                      val assoc1 = forallE(addAssoc)((n^^i) ^* evalh(p,l),evalh(r,drop(F)(l,j)),evalh(q,t))
                      val assoc2 = forallE(addAssoc)(evalh(r,drop(F)(l,j)),(n^^i) ^* evalh(p,l),evalh(q,t))
                      val deduct = 
                        (evalh(xi,l) ^+ evalh(yi,l)) ==| andI(isCons,assoc2,commute1,assoc1,commute2,commute) | 
                        (((n^^i) ^* evalh(p,l)) ^+ (evalh(q,t) ^+ evalh(r,drop(F)(l,j))))
                      val oneCase: Theorem = implI(j === E(BigInt(1))){ isOne =>
                        val lemma1 = strongHypFun(q,r,andI(axioms,hyp),t)
                        evalh(normadd(xi,yi),l)  ==| andI(isOne,isCons,lemma1,deduct,commute) |
                        (evalh(xi,l) ^+ evalh(yi,l))
                      }
                      val notOneCase: Theorem = implI(j > E(BigInt(1))){ notOne =>
                        val lemma2 = strongHypFun(q,POP(j-E(BigInt(1)),r),andI(axioms,hyp,notOne),t)
                        evalh(normadd(xi,yi),l) ==| andI(notOne,isCons,lemma2,deduct) |
                        (evalh(xi,l) ^+ evalh(yi,l))
                      }
                      andI(oneCase,notOneCase)
                    }
                    andI(nilCase,consCase)
                  case C(`POW_ID`,r,j,s) => 
                    val n = l.asInstOf(T(cons)(F)).getField(head)
                    val t = l.asInstOf(T(cons)(F)).getField(tail)
                    val hyp = andI(forallE(countLemma)(p),forallE(countLemma)(q),forallE(countLemma)(r),forallE(countLemma)(s))
                    val lemma7 = forallE(addAssoc)(((n^^i) ^* evalh(p,l)) ^+ ((n^^j) ^* evalh(r,l)),evalh(q,t),evalh(s,t))
                    val lemma8 = forallE(addAssoc)((n^^i) ^* evalh(p,l),(n^^j) ^* evalh(r,l),evalh(q,t))
                    val lemma9 = forallE(addC)((n^^j) ^* evalh(r,l),evalh(q,t))
                    val lemma10 = forallE(addAssoc)((n^^i) ^* evalh(p,l),evalh(q,t),(n^^j) ^* evalh(r,l))
                    val lemma11 = forallE(addAssoc)(((n^^i) ^* evalh(p,l)) ^+ evalh(q,t),(n^^j) ^* evalh(r,l),evalh(s,t))
                    val iEqj: Theorem = implI(i === j){ ieqj =>
                      val shfnormp1 = implE(forallE(normAddTheorem1)(p,r))(g => axioms)
                      val shfp1 = implE(forallE(normalityLemma)(normadd(p,r)))(g => shfnormp1)
                      val shfnormp2 = implE(forallE(normAddTheorem1)(q,s))(g => axioms)
                      val shfp2 = implE(forallE(normalityLemma)(normadd(q,s)))(g => shfnormp2)
                      val powlemma = forallE(normpow2Theorem)(i,normadd(p,r),normadd(q,s),l)
                      val firsthyp = prove(i > E(BigInt(0)) && 
                                           shfp(normadd(p,r)) && shfp(normadd(q,s)) &&
                                           shfnormp(normadd(p,r)) && shfnormp(normadd(q,s)),
                                           axioms, shfnormp1, shfnormp2, shfp1, shfp2 )
                      val secondhyp = andI(addO,addN,addAssoc,isDistr,multA,multN)
                      val lemma1 = prove(evalh(pow(normadd(p,r),i,normadd(q,s)), l) === evalh(POW(normadd(p,r),i,normadd(q,s)), l),
                                               powlemma,firsthyp,secondhyp)
                      val lemma2 = strongHypFun(p,r,andI(axioms,hyp),l)
                      val nilCase: Theorem = implI(l.isInstOf(T(nil)(F))){ isNil =>
                        val lemma2 = strongHypFun(q,s,andI(axioms,hyp),l)
                        evalh(normadd(xi,yi),l)    ==| andI(lemma1,ieqj,isNil) |
                        evalh(normadd(q,s),l)      ==| lemma2                  |
                        (evalh(q,l) ^+ evalh(s,l)) ==| isNil                   |
                        (evalh(xi,l) ^+ evalh(yi,l))
                      }
                      val consCase: Theorem = implI(l.isInstOf(T(cons)(F))){ isCons =>
                        val lemma3 = strongHypFun(q,s,andI(axioms,hyp),t)
                        val lemma4 = forallE(isDistr)(n^^i,evalh(p,l),evalh(r,l))
                        evalh(normadd(xi,yi),l) ==| andI(lemma1,ieqj,isCons,lemma2,lemma3) |
                        (((n^^i) ^* (evalh(p,l) ^+ evalh(r,l))) ^+ (evalh(q,t) ^+ evalh(s,t))) ==| 
                          andI(lemma4,lemma7,lemma8,lemma9,lemma10,lemma11,ieqj,isCons) |
                        (evalh(xi,l) ^+ evalh(yi,l))
                      }
                      prove(evalh(normadd(xi,yi),l) === (evalh(xi,l) ^+ evalh(yi,l)),
                            ieqj, nilCase, consCase)
                    }
                    
                    val iGreaterThanJ: Theorem = implI(i > j){ igtj =>
                      val shfnormp1 = implE(forallE(normAddTheorem1)(POW(p,i-j,constshf(z)),r))(g => andI(axioms,igtj))
                      val shfp1 = implE(forallE(normalityLemma)(normadd(POW(p,i-j,constshf(z)),r)))(g => shfnormp1)
                      val shfnormp2 = implE(forallE(normAddTheorem1)(q,s))(g => axioms)
                      val shfp2 = implE(forallE(normalityLemma)(normadd(q,s)))(g => shfnormp2)
                      val powlemma = forallE(normpow2Theorem)(j,normadd(POW(p,i-j,constshf(z)),r),normadd(q,s),l)
                      val firsthyp = prove(j > E(BigInt(0)) && 
                                           shfp(normadd(POW(p,i-j,constshf(z)),r)) && shfp(normadd(q,s)) &&
                                           shfnormp(normadd(POW(p,i-j,constshf(z)),r)) && shfnormp(normadd(q,s)),
                                           axioms, shfnormp1, shfnormp2, shfp1, shfp2 )
                      val secondhyp = andI(addO,addN,addAssoc,isDistr,multA,multN)
                      val lemma1 = prove(evalh(pow(normadd(POW(p,i-j,constshf(z)),r),j,normadd(q,s)), l) === 
                                         evalh(POW(normadd(POW(p,i-j,constshf(z)),r),j,normadd(q,s)), l),
                                         powlemma,firsthyp,secondhyp)
                      val nilCase: Theorem = implI(l.isInstOf(T(nil)(F))){ isNil =>
                        val lemma2 = strongHypFun(q,s,andI(axioms,hyp),l)
                        evalh(normadd(xi,yi),l)    ==| andI(lemma1,igtj,isNil) |
                        evalh(normadd(q,s),l)      ==| lemma2                  |
                        (evalh(q,l) ^+ evalh(s,l)) ==| isNil                   |
                        (evalh(xi,l) ^+ evalh(yi,l))
                      }
                      val consCase: Theorem = implI(l.isInstOf(T(cons)(F))){ isCons =>
                        val lemma2 = strongHypFun(POW(p,i-j,constshf(z)),r,andI(axioms,hyp,igtj),l)
                        val lemma3 = strongHypFun(q,s,andI(axioms,hyp),t)
                        val lemma12 = forallE(isDistr)(n^^j,(n ^^ (i-j)) ^* evalh(p,l),evalh(r,l))
                        val lemma13 = forallE(multA)(n^^j,n^^(i-j),evalh(p,l))
                        val auxiliar = prove((i-j) >= E(BigInt(0)) &&
                                             j >= E(BigInt(0)), 
                                             axioms,igtj)
                        val lemma14 = implE(forallE(exp2Theorem)(n,j,i-j))(g => andI(auxiliar,multN,multA))
                        val lemma15 = forallE(addN)((n ^^ (i-j)) ^* evalh(p,l))
                        evalh(normadd(xi,yi),l) ==| andI(lemma1,igtj,isCons,lemma2,lemma3,lemma15,lemma12,lemma13,lemma14) |
                        ((((n^^i) ^*  evalh(p,l)) ^+ ((n^^j) ^* evalh(r,l))) ^+ (evalh(q,t) ^+ evalh(s,t))) ==|
                          andI(lemma7,lemma8,lemma9,lemma10,lemma11,igtj,isCons) |
                        (evalh(xi,l) ^+ evalh(yi,l))
                      }
                      prove(evalh(normadd(xi,yi),l) === (evalh(xi,l) ^+ evalh(yi,l)),
                            igtj, nilCase, consCase)
                    }

                    val iLessThanJ: Theorem = implI(i < j){ iltj =>
                      val shfnormp1 = implE(forallE(normAddTheorem1)(POW(r,j-i,constshf(z)),p))(g => andI(axioms,iltj))
                      val shfp1 = implE(forallE(normalityLemma)(normadd(POW(r,j-i,constshf(z)),p)))(_ => shfnormp1)
                      val shfnormp2 = implE(forallE(normAddTheorem1)(s,q))(g => axioms)
                      val shfp2 = implE(forallE(normalityLemma)(normadd(s,q)))(g => shfnormp2)
                      val powlemma = forallE(normpow2Theorem)(i,normadd(POW(r,j-i,constshf(z)),p),normadd(s,q),l)
                      val firsthyp = prove(i > E(BigInt(0)) && 
                                           shfp(normadd(POW(r,j-i,constshf(z)),p)) && shfp(normadd(s,q)) &&
                                           shfnormp(normadd(POW(r,j-i,constshf(z)),p)) && shfnormp(normadd(s,q)),
                                           axioms, shfnormp1, shfnormp2, shfp1, shfp2 )
                      val secondhyp = andI(addO,addN,addAssoc,isDistr,multA,multN)
                      val lemma1 = prove(evalh(pow(normadd(POW(r,j-i,constshf(z)),p),i,normadd(s,q)), l) === 
                                         evalh(POW(normadd(POW(r,j-i,constshf(z)),p),i,normadd(s,q)), l),
                                         powlemma,firsthyp,secondhyp)
                      val nilCase: Theorem = implI(l.isInstOf(T(nil)(F))){ isNil =>
                        val lemma2 = strongHypFun(s,q,andI(axioms,hyp),l)
                        val lemma3 = forallE(addC)(evalh(s,l),evalh(q,l))
                        evalh(normadd(xi,yi),l)    ==| andI(lemma1,iltj,isNil) |
                        evalh(normadd(s,q),l)      ==| lemma2                  |
                        (evalh(s,l) ^+ evalh(q,l)) ==| andI(isNil,lemma3)      |
                        (evalh(xi,l) ^+ evalh(yi,l))
                      }
                      val lemma17 = forallE(addAssoc)(((n^^j) ^* evalh(r,l)) ^+ ((n^^i) ^* evalh(p,l)),evalh(s,t),evalh(q,t))
                      val lemma18 = forallE(addAssoc)((n^^j) ^* evalh(r,l),(n^^i) ^* evalh(p,l),evalh(s,t))
                      val lemma19 = forallE(addC)((n^^i) ^* evalh(p,l),evalh(s,t))
                      val lemma20 = forallE(addAssoc)((n^^j) ^* evalh(r,l),evalh(s,t),(n^^i) ^* evalh(p,l))
                      val lemma21 = forallE(addAssoc)(((n^^j) ^* evalh(r,l)) ^+ evalh(s,t),(n^^i) ^* evalh(p,l),evalh(q,t))
                      val consCase: Theorem = implI(l.isInstOf(T(cons)(F))){ isCons =>
                        val lemma2 = strongHypFun(POW(r,j-i,constshf(z)),p,andI(axioms,hyp,iltj),l)
                        val lemma3 = strongHypFun(s,q,andI(axioms,hyp),t)
                        val lemma4 = forallE(addC)(evalh(xi,l), evalh(yi,l))
                        val lemma12 = forallE(isDistr)(n^^i,(n ^^ (j-i)) ^* evalh(r,l),evalh(p,l))
                        val lemma13 = forallE(multA)(n^^i,n^^(j-i),evalh(r,l))
                        val auxiliar = prove((j-i) >= E(BigInt(0)) &&
                                             i >= E(BigInt(0)), 
                                             axioms,iltj)
                        val lemma14 = implE(forallE(exp2Theorem)(n,i,j-i))(g => andI(auxiliar,multN,multA))
                        val lemma15 = forallE(addN)((n ^^ (j-i)) ^* evalh(r,l))
                        evalh(normadd(xi,yi),l) ==| andI(lemma1,iltj,isCons,lemma2,lemma3,lemma15,lemma12,lemma13,lemma14) |
                        ((((n^^j) ^*  evalh(r,l)) ^+ ((n^^i) ^* evalh(p,l))) ^+ (evalh(s,t) ^+ evalh(q,t))) ==|
                          andI(lemma17,lemma18,lemma19,lemma20,lemma21,iltj,isCons,lemma4) |
                        (evalh(xi,l) ^+ evalh(yi,l))
                      }

                      prove(evalh(normadd(xi,yi),l) === (evalh(xi,l) ^+ evalh(yi,l)),
                            iltj, nilCase, consCase)
                    }

                    andI(iEqj,iGreaterThanJ,iLessThanJ)
              }}}}
            }}}}}
  // shnf(x,y) => evalh(normadd(x,y),l) == evalh(x,l) + evalh(y,l)
  lazy val normAddTheorem2: Theorem = 
    forallI("x" :: shf, "y" :: shf,"l" :: T(list)(F)){ case (x,y,l) => 
      implI(and(addCommutative,addAssociative,addNeutralElement,addOppositeElement,
                multAssociative,multNeutralElement,isDistributive,
                shfp(x),shfp(y),shfnormp(x),shfnormp(y))){ axioms =>
      val sum = shfCount(x) + shfCount(y)  
      val proposition = 
        evalh(normadd(x,y),l) === (evalh(x,l) ^+ evalh(y,l))
      val withoutHyp = implE(normAddLemma2)(g => axioms)
      val withoutMeasure = implE(forallE(withoutHyp)(sum))(_ =>
                                andI(forallE(countLemma)(x),forallE(countLemma)(y)))
      val instantiated = implE(forallE(withoutMeasure)(x,y,l))(_ => axioms)
      prove(proposition, instantiated)
    }}    
   
  // Theorems for normneg
  // normneg(normneg x) = x
  lazy val normnegInvolutionLemma: Theorem = 
    implI(and(addOppositeElement,addNeutralElement,addAssociative)){ axioms => 
      def property(p: Expr) = {
        normneg(normneg(p)) === p   
      }
      structuralInduction(property _, "p" :: shf) { case (ihs, _) =>
        ihs.expression match{
          case C(`constshfID`, fc) => 
            normneg(normneg(ihs.expression)) ==| trivial |
            constshf(opp(opp(fc))) ==| 
              forallE(implE(oppositeInvolutionLemma)(_ => axioms))(fc) |
            ihs.expression
          case C(`POP_ID`,i,pshf) => 
            normneg(normneg(ihs.expression)) ==| trivial |
            POP(i,normneg(normneg(pshf))) ==|
              ihs.hypothesis(pshf) |
            ihs.expression
          case C(`POW_ID`,pshf,i,qshf) => 
            normneg(normneg(ihs.expression)) ==| trivial |
            POW(normneg(normneg(pshf)),i,normneg(normneg(qshf))) ==|
              andI(ihs.hypothesis(pshf),ihs.hypothesis(qshf)) |
            ihs.expression
        }
      }
    }
  // normneg(z) = z
  lazy val negZeroLemma: Theorem = 
    implI(and(addOppositeElement,addNeutralElement,addAssociative)){ axioms =>
      normneg(constshf(z)) ==| trivial |
      constshf(opp(z))     ==| implE(oppositeOfZeroLemma)(_ => axioms) |
      constshf(z)
    }

  // shnf x => shnf normneg x
  lazy val normNeg1Lemma: Theorem = {
    implI(and(addOppositeElement,addNeutralElement,addAssociative)){ axioms =>
      def property(x: Expr) = {
        (shfp(x) && shfnormp(x)) ==> shfnormp(normneg(x))   
      }
      structuralInduction(property _, "x" :: shf) { case (ihs, _) =>
        val xi = ihs.expression 
        implI(shfp(xi) && shfnormp(xi)){ hyp =>
          xi match{
            case C(`constshfID`, _) => truth
            case C(`POP_ID`,_,p) => ihs.hypothesis(p)
            case C(`POW_ID`,p,i,q) => 
              def form(x: Expr): Expr = {
                val r = x.asInstOf(POW).getField(qshf)
                r.isInstOf(constshf) && (r.asInstOf(constshf).getField(fc) === z)
              }
              val lemma1 = implE(oppositeOfZeroLemma)(_ => axioms)
              val lemma2 = implE(ihs.hypothesis(p))(_ => hyp)
              val lemma3 = implE(ihs.hypothesis(q))(_ => hyp)
              val lemma4 = andI(lemma1,lemma2,lemma3,hyp,axioms)
              val lemma5 = forallE(implE(normnegInvolutionLemma)(_ => axioms))(p)
              val lemma6 = 
                (normneg(p).isInstOf(POW) && form(normneg(p))) ==| andI(lemma5,lemma1) |
                (p.isInstOf(POW) && form(p))
              andI(lemma4,lemma5,lemma1,lemma6)
          
          }}}}}      

  // shnf x => evalh(normneg x, vals) = - evalh(x,vals)
  lazy val normNeg2Lemma: Theorem = 
    implI(and(addOppositeElement,addNeutralElement,addAssociative,addCommutative,isDistributive)){ axioms =>
      val Seq(addO,addN,addA,addC,isDistr) = andE(axioms): Seq[Theorem]
      def property(p: Expr) = {
        forall("l" :: T(list)(F)){ case (l) => 
          (shfp(p) && shfnormp(p)) ==> (evalh(normneg(p),l) === opp(evalh(p,l)))
        }   
      }
      structuralInduction(property _, "p" :: shf) { case (ihs, _) =>
        val pi = ihs.expression
        forallI("l" :: T(list)(F)){ case (l) => 
        implI(shfp(pi) && shfnormp(pi)){ hypothesis => 
        pi match{
          case C(`constshfID`, _) => truth
          case C(`POP_ID`,i,pshf) => 
            evalh(normneg(pi),l)                ==| trivial                       |
            evalh(POP(i,normneg(pshf)),l)       ==| trivial                       |
            evalh(normneg(pshf),drop(F)(l,i))   ==| 
              implE(forallE(ihs.hypothesis(pshf))(drop(F)(l,i)))(g => hypothesis) |
            opp(evalh(pshf,drop(F)(l,i)))       ==| trivial                       |
            opp(evalh(pi,l))
          case C(`POW_ID`,pshf,i,qshf) => 
            val nilLemma: Theorem = implI(l.isInstOf(T(nil)(F))){ nilhyp => 
              evalh(normneg(pi),l)                                     ==| trivial |
              evalh(POW(normneg(pshf),i,normneg(qshf)),l)              ==| nilhyp  |
              evalh(normneg(qshf),l)                                   ==| 
                implE(forallE(ihs.hypothesis(qshf))(l))(g => hypothesis) | 
              opp(evalh(qshf,l))                                       ==| nilhyp  |
              opp(evalh(pi,l))
            }

            val consLemma: Theorem = implI(l.isInstOf(T(cons)(F))){ conshyp => 
              val h = l.asInstOf(T(cons)(F)).getField(head)
              val t = l.asInstOf(T(cons)(F)).getField(tail)
              evalh(normneg(pi),l)                                           ==| trivial |
              evalh(POW(normneg(pshf),i,normneg(qshf)),l)                    ==| conshyp |
              ((h ^^ i) ^* evalh(normneg(pshf),l) ^+ evalh(normneg(qshf),t)) ==| 
                andI(implE(forallE(ihs.hypothesis(pshf))(l))(g => hypothesis),
                     implE(forallE(ihs.hypothesis(qshf))(t))(g => hypothesis)) |         
              ((h ^^ i) ^* opp(evalh(pshf,l)) ^+ opp(evalh(qshf,t)))         ==| 
                forallE(implE(oppositeOfMultLemma)(g => axioms))(h ^^ i,evalh(pshf,l)) |
              (opp((h ^^ i) ^* evalh(pshf,l)) ^+ opp(evalh(qshf,t)))         ==| 
                forallE(implE(oppositeOfAddLemma)(g => axioms))(evalh(qshf,t),(h ^^ i) ^* evalh(pshf,l)) |
              (opp(evalh(qshf,t) ^+ ((h ^^ i) ^* evalh(pshf,l))))            ==| 
                andI(conshyp,forallE(addC)((h ^^ i) ^* evalh(pshf,l),evalh(qshf,t))) |
              opp(evalh(POW(pshf,i,qshf),l))
            }
            andI(nilLemma,consLemma)         
          }}}}}
  
  
  // theorems from the normmul definition
  // shnf(x,y) => shnf(normmul(x,y))
  lazy val normMulLemma1: Theorem = {
    def property(n: Expr): Expr = {
      forall("x" :: shf, "y" :: shf){ case (x,y) => 
        (n === shfCount(x) + shfCount(y) && 
         shfp(x) && shfp(y) && 
         shfnormp(x) && shfnormp(y)) ==> shfnormp(normmul(x,y))
      }
    }
    naturalInduction(property _, E(BigInt(0)),(_:Goal).by(countLemma)) { case (ihs, _) =>
      val n = ihs.variable
      val next = n + E(BigInt(1))
      def strongHypFun(a: Expr, b: Expr,lemma: Theorem): Theorem = {
        val m = shfCount(a) + shfCount(b)
        implE(forallE(implE(forallE(ihs.propertyForLessOrEqualToVar)(m))( _ =>
          lemma))(a,b))(_ => lemma)
      }
      def property1(x: Expr): Expr = forall("y" :: shf){ case (y) => 
        (next === shfCount(x) + shfCount(y) && 
        shfp(x) && shfp(y) && 
        shfnormp(x) && shfnormp(y)) ==> shfnormp(normmul(x,y))
      }
      structuralInduction(property1 _, "x" :: shf) { case (ihs1, goal1) =>
        val xi = ihs1.expression
        def property2(y: Expr): Expr = {
          (next === shfCount(xi) + shfCount(y) && 
          shfp(xi) && shfp(y) && 
          shfnormp(xi) && shfnormp(y)) ==> shfnormp(normmul(xi,y))
        }
        xi match{
          case C(`constshfID`, _) =>
            structuralInduction(property2 _, "y" :: shf) { case (ihs2, _) =>
              val yi = ihs2.expression
              implI(and(next === shfCount(xi) + shfCount(yi),
                      shfp(xi),shfp(yi),
                      shfnormp(xi),shfnormp(yi))){ axioms =>
              val Seq(ind,shfx,shfy,shfnormx,shfnormy): Seq[Theorem] = andE(axioms)
              yi match{
                case C(`constshfID`, _) => truth
                case C(`POP_ID`,i,p) => 
                  val lemma = andI(axioms,forallE(countLemma)(p))
                  val strongLemma = strongHypFun(xi,p,lemma)
                  val normalLemma = implE(forallE(normalityLemma)(normmul(xi,p)))(_ => strongLemma)
                  implE(forallE(normpop1Lemma)(i,normmul(xi,p)))(_ =>
                    andI(shfy,strongLemma,normalLemma))
                case C(`POW_ID`,p,i,q) => 
                  val lemma = andI(axioms,forallE(countLemma)(p),forallE(countLemma)(q))
                  val strongLemma1 = strongHypFun(xi,p,lemma)
                  val normalLemma1 = implE(forallE(normalityLemma)(normmul(xi,p)))(_ => strongLemma1)
                  val strongLemma2 = strongHypFun(xi,q,lemma)
                  val normalLemma2 = implE(forallE(normalityLemma)(normmul(xi,q)))(_ => strongLemma2)
                  implE(forallE(normpow1Lemma)(normmul(xi,p),i,normmul(xi,q)))(_ =>
                    andI(shfnormy,strongLemma1,strongLemma2,normalLemma1,normalLemma2))
                }
            }}
            case C(`POP_ID`,i,p) => 
              structuralInduction(property2 _, "p" :: shf) { case (ihs2, _) =>
                val yi = ihs2.expression
                implI(and(next === shfCount(xi) + shfCount(yi), 
                       shfp(xi), shfp(yi), 
                       shfnormp(xi), shfnormp(yi))){ axioms =>
                val Seq(ind,shfx,shfy,shfnormx,shfnormy): Seq[Theorem] = andE(axioms)
                yi match {
                  case C(`constshfID`, c) => 
                    val lemma = andI(axioms,forallE(countLemma)(p))
                    val strongLemma = strongHypFun(yi,p,lemma)
                    val normalLemma = 
                      implE(forallE(normalityLemma)(normmul(yi,p)))(_ => strongLemma)
                    implE(forallE(normpop1Lemma)(i,normmul(yi,p)))(_ =>
                      andI(shfx,strongLemma,normalLemma))
                  case C(`POP_ID`,j,q) => 
                    val lemma = andI(axioms,forallE(countLemma)(p),forallE(countLemma)(q))
                    val strongHyp1 = strongHypFun(p,q,lemma) 
                    val strongHyp2 = implI(i > j){ igtj => 
                      strongHypFun(POP(i-j,p),q,andI(lemma,igtj))
                    } 
                    val strongHyp3 = implI(i < j){ iltj => 
                      strongHypFun(POP(j-i,q),p,andI(lemma,iltj))  
                    }  
                    andI(strongHyp1,strongHyp2,strongHyp3)
                  case C(`POW_ID`,q,j,r) => 
                    val lemma = andI(axioms,forallE(countLemma)(r),forallE(countLemma)(p),forallE(countLemma)(q))
                    val strongHyp1 = strongHypFun(p,r,lemma) 
                    val shfp1 = implE(forallE(normalityLemma)(normmul(p,r)))(_ => strongHyp1)
                    val strongHyp2 = implI(i > E(BigInt(1))){ igt1 =>
                      strongHypFun(POP(i-E(BigInt(1)),p),r,andI(lemma,igt1)) 
                    }
                    val shfp2 = implI(i > E(BigInt(1))){ igt1 =>
                      implE(forallE(normalityLemma)(normmul(POP(i-E(BigInt(1)),p),r)))(_ => andI(strongHyp2,igt1))
                    }  
                    val strongHyp3 = strongHypFun(xi,q,lemma)
                    val shfp3 = implE(forallE(normalityLemma)(normmul(xi,q)))(_ => strongHyp3)
                    val auxiliar = prove(j > E(BigInt(0)),shfnormy)
                    val lemma1 = 
                      implE(forallE(normpow1Lemma)(normmul(xi,q),j,normmul(p,r)))(_ =>
                        andI(auxiliar,strongHyp1,shfp1,strongHyp3,shfp3))
                    val lemma2 = 
                      implI(i > E(BigInt(1))){ igt1 => 
                        implE(forallE(normpow1Lemma)(normmul(xi,q),j,normmul(POP(i-E(BigInt(1)),p),r)))(_ =>
                          andI(strongHyp3,shfp3,implE(strongHyp2)(_ => igt1),
                               implE(shfp2)(_ => igt1),auxiliar))
                    }
                    andI(lemma1,lemma2)
                }
              }}
            case C(`POW_ID`,p,i,q) => 
              structuralInduction(property2 _, "p" :: shf) { case (ihs2, _) =>
                val yi = ihs2.expression
                implI(and(next === shfCount(xi) + shfCount(yi),
                       shfp(xi),shfp(yi),
                       shfnormp(xi),shfnormp(yi))){ axioms =>
                val Seq(ind,shfx,shfy,shfnormx,shfnormy): Seq[Theorem] = andE(axioms)
                yi match{
                  case C(`constshfID`, c) => 
                    val lemma = andI(axioms,forallE(countLemma)(p),forallE(countLemma)(q))
                    val strongLemma1 = strongHypFun(yi,p,lemma)
                    val normalLemma1 = implE(forallE(normalityLemma)(normmul(yi,p)))(_ => strongLemma1)
                    val strongLemma2 = strongHypFun(yi,q,lemma)
                    val normalLemma2 = implE(forallE(normalityLemma)(normmul(yi,q)))(_ => strongLemma2)
                    implE(forallE(normpow1Lemma)(normmul(yi,p),i,normmul(yi,q)))(_ =>
                      andI(shfnormx,strongLemma1,strongLemma2,normalLemma1,normalLemma2))
                  case C(`POP_ID`,j,r) => 
                    val lemma = andI(axioms,forallE(countLemma)(r),forallE(countLemma)(p),forallE(countLemma)(q))
                    val strongHyp1 = strongHypFun(r,q,lemma) 
                    val shfp1 = implE(forallE(normalityLemma)(normmul(r,q)))(_ => strongHyp1)
                    val strongHyp2 = implI(j > E(BigInt(1))){ igt1 =>
                      strongHypFun(POP(j-E(BigInt(1)),r),q,andI(lemma,igt1)) 
                    }
                    val shfp2 = implI(j > E(BigInt(1))){ igt1 =>
                      implE(forallE(normalityLemma)(normmul(POP(j-E(BigInt(1)),r),q)))(_ => andI(strongHyp2,igt1))
                    }  
                    val strongHyp3 = strongHypFun(yi,p,lemma)
                    val shfp3 = implE(forallE(normalityLemma)(normmul(yi,p)))(_ => strongHyp3)
                    val lemma1 = 
                      implE(forallE(normpow1Lemma)(normmul(yi,p),i,normmul(r,q)))(_ =>
                        andI(shfnormx,strongHyp1,shfp1,strongHyp3,shfp3))
                    val lemma2 = 
                      implI(j > E(BigInt(1))){ igt1 => 
                        implE(forallE(normpow1Lemma)(normmul(yi,p),i,normmul(POP(j-E(BigInt(1)),r),q)))(_ =>
                          andI(strongHyp3,shfp3,implE(strongHyp2)(_ => igt1),
                               implE(shfp2)(_ => igt1),shfnormx))
                    }
                    andI(lemma1,lemma2)
                  case C(`POW_ID`,r,j,s) => 
                    val lemma = andI(axioms,forallE(countLemma)(q),forallE(countLemma)(r),
                                        forallE(countLemma)(p),forallE(countLemma)(s))
                    val strongHyp1 = strongHypFun(p,r,lemma) 
                    val shfp1 = implE(forallE(normalityLemma)(normmul(p,r)))(_ => strongHyp1)
                    val strongHyp2 = strongHypFun(q,s,lemma)
                    val shfp2 = implE(forallE(normalityLemma)(normmul(q,s)))(_ => strongHyp2)
                    val pop1 = implE(forallE(normpop1Lemma)(E(BigInt(1)),s))(_ => andI(shfnormy,shfy))
                    val pop2 = implE(forallE(normpop1Lemma)(E(BigInt(1)),q))(_ => andI(shfnormx,shfx))
                    val strongHyp3 = strongHypFun(p,pop(E(BigInt(1)),s),andI(lemma,pop1))
                    val shfp3 = implE(forallE(normalityLemma)(normmul(p,pop(E(BigInt(1)),s))))(_ => strongHyp3)
                    val strongHyp4 = strongHypFun(r,pop(E(BigInt(1)),q),andI(lemma,pop2)) 
                    val shfp4 = implE(forallE(normalityLemma)(normmul(r,pop(E(BigInt(1)),q))))(_ => strongHyp4)
                    val fterm = pow(normmul(p,r),i+j,normmul(q,s))
                    val sterm = pow(normmul(p,pop(E(BigInt(1)),s)),i,constshf(z))
                    val tterm = pow(normmul(r,pop(E(BigInt(1)),q)),j,constshf(z))
                    val lemma1 = 
                      implE(forallE(normpow1Lemma)(normmul(p,r),i+j,normmul(q,s)))(_ =>
                        andI(shfnormx,shfnormy,strongHyp1,shfp1,strongHyp2,shfp2))
                    val shfpl1 = implE(forallE(normalityLemma)(fterm))(_ => lemma1)
                    val lemma2 = 
                      implE(forallE(normpow1Lemma)(normmul(p,pop(E(BigInt(1)),s)),i,constshf(z)))(_ =>
                        andI(shfnormx,strongHyp3,shfp3))
                    val shfpl2 = implE(forallE(normalityLemma)(sterm))(_ => lemma2)
                    val lemma3 = 
                      implE(forallE(normpow1Lemma)(normmul(r,pop(E(BigInt(1)),q)),j,constshf(z)))(_ =>
                        andI(shfnormy,strongHyp4,shfp4))
                    val shfpl3 = implE(forallE(normalityLemma)(tterm))(_ => lemma3)
                    val lemma4 = implE(forallE(normAddTheorem1)(fterm,sterm))(_ =>
                                        andI(lemma1,lemma2,shfpl1,shfpl2))
                    val shfpl4 = implE(forallE(normalityLemma)(normadd(fterm,sterm)))(_ => lemma4)
                    val lemma5 = implE(forallE(normAddTheorem1)(
                                    normadd(fterm,sterm),tterm))(_ =>
                                    andI(lemma4,lemma3,shfpl3,shfpl4))   
                    lemma5
                }
              }}}}}}            
  // shnf(x,y) => shnf(normmul(x,y))
  lazy val normMulTheorem1: Theorem = 
    forallI("x" :: shf, "y" :: shf){ case (x,y) => 
      val sum = shfCount(x) + shfCount(y)  
      val proposition = 
        (shfp(x) && shfp(y) && shfnormp(x) && shfnormp(y)) ==> 
          shfnormp(normmul(x,y))    
      val proof = 
        implE(forallE(normMulLemma1)(sum))(_ =>
          andI(forallE(countLemma)(x),forallE(countLemma)(y)))
      prove(proposition, proof)
    }    


  // shnf(x,y) => evalh(normmul(x,y),vals) = evalh(x,vals) * evalh(y,vals)
  lazy val normMulLemma2: Theorem = {
    implI(and(addCommutative,addAssociative,addNeutralElement,addOppositeElement,
              multAssociative, multNeutralElement,isDistributive)){ addMultAxioms =>
    val Seq(addC,addAssoc,addN,addO,multA,multN,isDistr): Seq[Theorem] = andE(addMultAxioms) 
    def property(n: Expr): Expr = {
      forall("x" :: shf, "y" :: shf,"l" :: T(list)(F)){ case (x,y,l) => 
        (n === (shfCount(x) + shfCount(y)) && shfp(x) && shfp(y) && shfnormp(x) && shfnormp(y)) ==>
          (evalh(normmul(x,y),l) === (evalh(x,l) ^* evalh(y,l)))
      }
    }
    naturalInduction(property _, E(BigInt(0)),(_:Goal).by(countLemma)) { case (ihs, _) =>
      val n = ihs.variable
      val next = n + E(BigInt(1))
      def strongHypFun(a: Expr, b: Expr,axioms: Theorem,l: Expr): Theorem = {
        val m = shfCount(a) + shfCount(b)
        implE(forallE(implE(forallE(ihs.propertyForLessOrEqualToVar)(m))(_ =>
          andI(axioms)))(a,b,l))(_ => axioms)
      }
      def property1(x: Expr): Expr = 
        forall("y" :: shf,"l" :: T(list)(F)){ case (y,l) => 
          (next === (shfCount(x) + shfCount(y)) && shfp(x) && shfp(y) && shfnormp(x) && shfnormp(y)) ==>
            (evalh(normmul(x,y),l) === (evalh(x,l) ^* evalh(y,l)))
        }
        structuralInduction(property1 _, "x" :: shf) { case (ihs1, _) =>
          val xi = ihs1.expression
          def property2(y: Expr): Expr = {
            forall("l" :: T(list)(F)){ case (l) =>
              (next === (shfCount(xi) + shfCount(y)) && shfp(xi) && shfp(y) && shfnormp(xi) && shfnormp(y)) ==> 
                (evalh(normmul(xi,y),l) === (evalh(xi,l) ^* evalh(y,l)))
            }  
          }
          xi match{
            case C(`constshfID`, c) =>          
              structuralInduction(property2 _, "y" :: shf) { case (ihs2, _) =>
                val yi = ihs2.expression
                forallI("l" :: T(list)(F)){ case (l) => 
                implI(and(next === (shfCount(xi) + shfCount(yi)),shfp(xi),shfp(yi),shfnormp(xi),shfnormp(yi))){ case axioms => 
                val Seq(ind,shfx,shfy,shfnormx,shfnormy): Seq[Theorem] = andE(axioms)
                yi match{
                  case C(`constshfID`, _) => truth
                  case C(`POP_ID`,i,p) => 
                    val lemma1 = implE(forallE(normMulTheorem1)(xi,p))(_ => axioms)
                    val shfp1 = implE(forallE(normalityLemma)(normmul(xi,p)))(_ => lemma1)
                    val pop1 = implE(forallE(normpop2Lemma)(i,normmul(xi,p),l))(_ => andI(shfp1,shfnormy))
                    val hyp = forallE(countLemma)(p)
                    val induct = strongHypFun(xi,p,andI(axioms,hyp),drop(F)(l,i))
                    evalh(normmul(xi,yi),l)                          ==| pop1   |
                    evalh(normmul(xi,p),drop(F)(l,i))                 ==| induct |
                    (evalh(xi,drop(F)(l,i)) ^* evalh(p,drop(F)(l,i))) 
                  case C(`POW_ID`,p,i,q) => 
                    val hyp = andI(forallE(countLemma)(p),forallE(countLemma)(q))
                    val lemma1 = implE(forallE(normMulTheorem1)(xi,p))(_ => axioms)
                    println(lemma1)
                    val shfp1 = implE(forallE(normalityLemma)(normmul(xi,p)))(_ => lemma1)
                    println(shfp1)
                    val lemma2 = implE(forallE(normMulTheorem1)(xi,q))(_ => axioms)
                    println(lemma2)
                    val shfp2 = implE(forallE(normalityLemma)(normmul(xi,q)))(_ => lemma2)
                    println(shfp2)
                    val induct2 = strongHypFun(xi,q,andI(axioms,hyp),l)
                    println(induct2)
                    val aux = prove(i > E(BigInt(0)) && 
                                    shfp(normmul(xi,p)) &&
                                    shfnormp(normmul(xi,p)) &&
                                    shfp(normmul(xi,q)) &&
                                    shfnormp(normmul(xi,q)),
                                    shfnormy,lemma1,shfp1,lemma2,shfp2)
                                      
                    println(aux)
                    val aux2 = normpow2Theorem
                    println(aux2)
                    val pow1 = implE(forallE(aux2)(i,normmul(xi,p),normmul(xi,q),l))(_ =>
                                      andI(aux,addMultAxioms))
                    println(pow1)
                    val nilCase: Theorem = implI(l.isInstOf(T(nil)())){ isNil =>
                      evalh(normmul(xi,yi),l)                    ==| pow1    |
                      evalh(POW(normmul(xi,p),i,normmul(xi,q)),l) ==| isNil   |
                      evalh(normmul(xi,q),l)                     ==| induct2 |
                      (evalh(xi,l) ^* evalh(q,l))                ==| isNil   |
                      (evalh(xi,l) ^* evalh(yi,l))
                    }
                    println(nilCase)
                    nilCase
              }}}}
            case C(`POP_ID`,i,p) => 
              structuralInduction(property2 _, "p" :: shf) { case (ihs2, _) =>
                val yi = ihs2.expression
                forallI("l" :: T(list)(F)){ case (l) => 
                implI(next === (shfCount(xi) + shfCount(yi)) && shfp(xi) && shfp(yi) && shfnormp(xi) && shfnormp(yi)){ case axioms => 
                yi match {
                  case C(`constshfID`, c) => truth
                  case C(`POP_ID`,j,q) => truth
                  case C(`POW_ID`,q,j,r) => truth

              }}}}
            case C(`POW_ID`,p,i,q) => 
              structuralInduction(property2 _, "p" :: shf) { case (ihs2, goal) =>
                val yi = ihs2.expression
                forallI("l" :: T(list)(F)){ case (l) => 
                implI(next === (shfCount(xi) + shfCount(yi)) && shfp(xi) && shfp(yi) && shfnormp(xi) && shfnormp(yi)){ case axioms => 
                yi match{
                  case C(`constshfID`, _) => truth
                  case C(`POP_ID`,_,_) => truth
                  case C(`POW_ID`,_,_,_) => truth

              }}}}
            }}}}}    

  // theorems from the normexpt definition
  // shnf(x) => shnf(normexpt(x,k))  
  lazy val normexpt1Lemma: Theorem = {
    def property(n: Expr): Expr = {
      forall("x" :: shf){ case (x) => 
        (shfp(x) && shfnormp(x)) ==> shfnormp(normexpt(x,n))
      }
    }
    naturalInduction(property _, E(BigInt(0)),trivial) { case (ihs, _) =>
      val n = ihs.variable
      val next = n + E(BigInt(1))
      forallI("x" :: shf){ case (x) => 
        implI(shfp(x) && shfnormp(x)){ axioms =>
          val induct = implE(forallE(ihs.propertyForVar)(x))(_ => axioms)
          val shfp1 = implE(forallE(normalityLemma)(normexpt(x,n)))(g => induct)
          implE(forallE(normMulTheorem1)(x,normexpt(x,n)))(g => andI(axioms,shfp1,induct))
        }
      }  
    }
  }

  lazy val normexptTheorem1 = prove(
    forall("x" :: shf, "n" :: IntegerType){ case (x,n) => 
      (n >= E(BigInt(0)) && shfp(x) && shfnormp(x)) ==>
        shfnormp(normexpt(x,n))  
    },normexpt1Lemma
  )     
  // shnf x => evalh(normexpt(x,k),l) = evalh(x,l)^^k

  // theorems from the norm definition
  // polyp(x,vars) && distinct-symbols(vars) => shnfp(norm(x,vars))
  // distinct-symbols(vars) && all-integers(vals) && len(vars) <= len(vals) && polyp(x,vars) => 
  //    shnf(norm(x,vars)) && evalh(norm(x,vars),vals) = evalp(x,zip(vars,vals))

}
