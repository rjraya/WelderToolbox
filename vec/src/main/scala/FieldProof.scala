import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object FieldProof {  
  import Field._
  import Register._
  import theory._
  
  //Think how to convert in generic properties for function
  //Extra parenthesis are needed for Welder to type well our expressions
  /* Lemma 1: The set of field elements with zero, opposite and addition is an abelian group
                      isPlusAbelianGroup(z, oppf, addf)
     Lemma 2: The set of non zero elements of the field with one, inverse and multiplication by 
              a non zero element forms a group. 
                      isStarAbelianGroup(z, one, invf, multf)    
     Lemma 3: The set of field elements with zero, one, opposite, addition, inverse and 
              multiplication is a commutative field.        
  */
  lazy val addAssociative: Expr = forall("x" :: F, "y" :: F, "z" :: F){ case (x, y, z) =>
    (x ^+ (y ^+ z)) === ((x ^+ y) ^+ z)
  }

  lazy val addNeutralElement: Expr = forall("x" :: F){ case (x) =>
    ((x ^+ z) === x) && ((z ^+ x) === x)
  }

  lazy val addOppositeElement: Expr = forall("x" :: F){ case (x) =>
    ((opp(x) ^+ x) === z) && ((x ^+ opp(x)) === z)
  }

  lazy val addCommutative: Expr = forall("x" :: F, "y" :: F){ case (x, y) =>
    (x ^+ y) === (y ^+ x)
  }

  lazy val addAbelianGroup: Expr = addAssociative &&
                              addNeutralElement &&
                              addOppositeElement && 
                              addCommutative
                                                                                                    
  lazy val multAssociative: Expr = forall("x" :: F, "y" :: F, "z" :: F){ case (x, y, z) =>
    (x ^* (y ^* z)) === ((x ^* y) ^* z)
  }

  lazy val multNeutralElement: Expr = forall("x" :: F){ case (x) =>
    ((x ^* one) === x) && ((one ^* x) === x)
  }

  lazy val multInverseElement: Expr = forall("x" :: F){ case (x) =>
    (x !== z) ==> {((inv(x) ^* x) === one) && ((x ^* inv(x)) === one)}
  }

  lazy val multCommutative: Expr = forall("x" :: F, "y" :: F){ case (x, y) =>
    (x ^* y) === (y ^* x)
  }

  lazy val multAbelianGroup: Expr = multAssociative &&
                               multNeutralElement &&
                               multInverseElement &&
                               multCommutative
                                                                     
  lazy val isDistributive: Expr = forall("x" :: F, "y" :: F, "z" :: F){ case (x, y, z) =>
    {(x ^* (y ^+ z)) === ((x ^* y) ^+ (x ^* z))} && {((x ^+ y) ^* z) === ((x ^* z) ^+ (y ^* z))}
  }

  lazy val zeroNotOne: Expr = (z !== one)

  lazy val isCommutativeField: Expr = addAbelianGroup &&
                                 multAbelianGroup &&
                                 zeroNotOne &&
                                 isDistributive
  //Further assume that the field hasn't got characteristic 2 or 3.
  //More elegant to write a function that computes the characteristic of the field.
  //For now we just assume characteristic is not 2.
  lazy val notCharacteristic2: Expr = ((one ^+ one) !== z)

  //The neutral element is unique.
  lazy val uniqueAddNeutralLemma: Theorem = 
    implI(addNeutralElement){ zeroIsNeutral =>
      forallI("y" :: F){ case (y) =>
        implI(forall("x" :: F){ case (x) =>
          ((x ^+ y) === x) && ((y ^+ x) === x)
        }){ yIsNeutral => 
          z ==| forallE(yIsNeutral)(z) | (z ^+ y) ==| forallE(zeroIsNeutral)(y) | y
        }
      }
    }

    //The inverse element is unique.
    lazy val uniqueMultInverseLemma: Theorem = 
      implI(and(multInverseElement,multNeutralElement,multAssociative)){ axioms =>
        val Seq(multInverseElement,multNeutralElement,multAssociative) = andE(axioms) : Seq[Theorem]
        forallI("x" :: F,"i1" :: F, "i2" :: F){ case (x,i1,i2) => 
          implI(
            (x !== z) && ((x ^* i1) === one) && ((i1 ^* x) === one) && ((x ^* i2) === one) && ((i2 ^* x) === one)
          ){ i1Andi2Inverse => 
            i1                ==| forallE(multNeutralElement)(i1)             | 
            (i1 ^* one)       ==| i1Andi2Inverse                              |
            (i1 ^* (x ^* i2)) ==| forallE(multAssociative)(i1,x,i2)           |
            ((i1 ^* x) ^* i2) ==| i1Andi2Inverse                              |  
            (one ^* i2)       ==| forallE(multNeutralElement)(i2)             |
            i2
          }
        }  
      }
    //The opposite element is unique.
    lazy val uniqueAddOppositeLemma: Theorem = 
      implI(and(addOppositeElement,addNeutralElement,addAssociative)){ axioms =>
        val Seq(addOppositeElement, addNeutralElement, addAssociative) = andE(axioms) : Seq[Theorem]
        forallI("x" :: F,"i1" :: F, "i2" :: F){ case (x,i1,i2) => 
          implI(
            ((x ^+ i1) === z) && ((i1 ^+ x) === z) && ((x ^+ i2) === z) && ((i2 ^+ x) === z)
          ){ i1Andi2Opposite => 
            i1                ==| forallE(addNeutralElement)(i1)              | 
            (i1 ^+ z)         ==| i1Andi2Opposite                             |
            (i1 ^+ (x ^+ i2)) ==| forallE(addAssociative)(i1,x,i2)            |
            ((i1 ^+ x) ^+ i2) ==| i1Andi2Opposite                             |  
            (z ^+ i2)         ==| forallE(addNeutralElement)(i2)              |
            i2
          }
        }  
      }

    //The opposite of zero is zero
    lazy val oppositeOfZeroLemma: Theorem =
      implI(and(addOppositeElement,addNeutralElement,addAssociative)){ axioms =>
        val Seq(addOppositeElement,addNeutralElement,addAssociative) = andE(axioms) : Seq[Theorem]
        opp(z) ==| andI(forallE(addOppositeElement)(z),
                        forallE(addNeutralElement)(z),
                        forallE(implE(uniqueAddOppositeLemma)(g => axioms))(z,opp(z),z)) |
        z
      }
   
    //opp(opp(x)) === x
    lazy val oppositeInvolutionLemma: Theorem = 
      implI(and(addOppositeElement,addNeutralElement,addAssociative)){ axioms =>
        val Seq(addOppositeElement,addNeutralElement,addAssociative) = andE(axioms) : Seq[Theorem]
        forallI("x" :: F){ case (x) => 
          opp(opp(x)) ==| andI(forallE(addOppositeElement)(opp(x)), 
                          forallE(addOppositeElement)(x),
                          forallE(implE(uniqueAddOppositeLemma)(g => axioms))(opp(x),x,opp(opp(x)))) |
          x
        }
      }
    // In a ring if x = 2x then x = 0
    lazy val simplificationLemma: Theorem = 
      implI(and(addOppositeElement,addNeutralElement,addAssociative)){ axioms =>
        val Seq(addOppositeElement,addNeutralElement,addAssociative) = andE(axioms) : Seq[Theorem]
        forallI("x" :: F){ case (x) => 
          implI(double(x) === x){ hypothesis =>
            z                    ==| forallE(addOppositeElement)(x)      |
            (x ^+ opp(x))        ==| hypothesis                          |
            ((x ^+ x) ^+ opp(x)) ==| forallE(addAssociative)(x,x,opp(x)) |
            (x ^+ (x ^+ opp(x))) ==| forallE(addOppositeElement)(x)      |
            (x ^+ z)             ==| forallE(addNeutralElement)(x)       |
            x
          }
        }
      }
    //In a ring we have for all a. a0 = 0 = 0a 
    lazy val zeroDivisorLemma: Theorem = 
      implI(and(addOppositeElement,addNeutralElement,
                addAssociative,isDistributive)){ axioms =>
        val Seq(addOppositeElement,addNeutralElement,
                addAssociative,isDistributive) = andE(axioms) : Seq[Theorem]

        forallI("x" :: F){ case (x) => 
          val deduction = (x ^* z)               ==| forallE(addNeutralElement)(z)  |
                          (x ^* (z ^+ z))        ==| forallE(isDistributive)(x,z,z) |
                          ((x ^* z) ^+ (x ^* z))  
          //to avoid introducing commutativity we repeat some code
          val symDeduction = (z ^* x)               ==| forallE(addNeutralElement)(z)  |
                             ((z ^+ z) ^* x)        ==| forallE(isDistributive)(z,z,x) |
                             ((z ^* x) ^+ (z ^* x))
          val implication = forallE(implE(simplificationLemma)(g => axioms))((x ^* z))
          val symImplication = forallE(implE(simplificationLemma)(g => axioms))((z ^* x))
          andI((x ^* z) ==| andI(deduction,implication) | z,
               (z ^* x) ==| andI(symDeduction,symImplication) | z)

        }
      }

    //In a ring -(a+b) = (-b) + (-a) (this forms avoids commutativity as much as possible)
    lazy val oppositeOfAddLemma: Theorem = 
      implI(and(addOppositeElement,addNeutralElement,addAssociative)){ axioms =>
        val Seq(addOppositeElement,addNeutralElement,addAssociative) = andE(axioms) : Seq[Theorem]
        forallI("a"::F,"b"::F){ case (a,b) => 
        val deduction = 
          ((a ^+ b) ^+ (opp(b) ^+ opp(a))) ==| forallE(addAssociative)(a,b,(opp(b) ^+ opp(a))) |
          (a ^+ (b ^+ (opp(b) ^+ opp(a)))) ==| forallE(addAssociative)(b,opp(b),opp(a))        |
          (a ^+ ((b ^+ opp(b)) ^+ opp(a))) ==| forallE(addOppositeElement)(b)                  |
          (a ^+ (z ^+ opp(a)))             ==| forallE(addAssociative)(a,z,opp(a))             |  
          ((a ^+ z) ^+ opp(a))             ==| forallE(addNeutralElement)(a)                   |
          (a ^+ opp(a))                    ==| forallE(addOppositeElement)(a)                  |
          z
      val symDeduction = 
          ((opp(b) ^+ opp(a)) ^+ (a ^+ b)) ==| forallE(addAssociative)(opp(b),opp(a),(a ^+ b)) |
          (opp(b) ^+ (opp(a) ^+ (a ^+ b))) ==| forallE(addAssociative)(opp(a),a,b)             |
          (opp(b) ^+ ((opp(a) ^+ a) ^+ b)) ==| forallE(addOppositeElement)(a)                  |
          (opp(b) ^+ (z ^+ b))             ==| forallE(addNeutralElement)(b)                   |
          (opp(b) ^+ b)                    ==| forallE(addOppositeElement)(b)                  |
          z

      val implication = forallE(implE(uniqueAddOppositeLemma)(g => axioms))((a ^+ b), opp(a ^+ b), (opp(b) ^+ opp(a)))
      val assumption = andI(forallE(addOppositeElement)((a ^+ b)),deduction,symDeduction)

      opp(a ^+ b) ==| andI(assumption, implication) | (opp(b) ^+ opp(a))
      }
    }

    //In a ring -(ab) = (-a)b = a(-b) 
    lazy val oppositeOfMultLemma: Theorem =
      implI(and(addOppositeElement,addNeutralElement,addAssociative,isDistributive)){ axioms =>
        val Seq(addOppositeElement,addNeutralElement,addAssociative,isDistributive) = andE(axioms) : Seq[Theorem]
        forallI("a"::F,"b"::F){ case (a,b) => 
        val deduction = 
          ((a ^* b) ^+ (opp(a) ^* b)) ==| forallE(isDistributive)(a,opp(a),b)              |
          ((a ^+ opp(a)) ^* b)        ==| forallE(addOppositeElement)(a)                   |
          (z ^* b)                    ==| forallE(implE(zeroDivisorLemma)(g => axioms))(b) |
          z
        val commDeduction = 
          ((opp(a) ^* b) ^+ (a ^* b)) ==| forallE(isDistributive)(opp(a),a,b)              |
          ((opp(a) ^+ a) ^* b)        ==| forallE(addOppositeElement)(a)                   |
          (z ^* b)                    ==| forallE(implE(zeroDivisorLemma)(g => axioms))(b) |
          z
        val symDeduction = 
          ((a ^* b) ^+ (a ^* opp(b))) ==| forallE(isDistributive)(a,b,opp(b))              |
          (a ^* (b ^+ opp(b)))        ==| forallE(addOppositeElement)(b)                   |
          (a ^* z)                    ==| forallE(implE(zeroDivisorLemma)(g => axioms))(a) |
          z
        val symCommDeduction = 
          ((a ^* opp(b)) ^+ (a ^* b)) ==| forallE(isDistributive)(a,opp(b),b)              |
          (a ^* (opp(b) ^+ b))        ==| forallE(addOppositeElement)(b)                   |
          (a ^* z)                    ==| forallE(implE(zeroDivisorLemma)(g => axioms))(a) |
          z

        val implication1 = forallE(implE(uniqueAddOppositeLemma)(g => axioms))((a ^* b), opp(a ^* b), (opp(a) ^* b))
        val assumption1 = andI(forallE(addOppositeElement)((a ^* b)),deduction,commDeduction)

        val implication2 = forallE(implE(uniqueAddOppositeLemma)(g => axioms))((a ^* b), opp(a ^* b), (a ^* opp(b)))
        val assumption2 = andI(forallE(addOppositeElement)((a ^* b)),symDeduction,symCommDeduction)

        andI({opp(a ^* b) ==| andI(assumption1, implication1) | (opp(a) ^* b)},
        {opp(a ^* b) ==| andI(assumption2, implication2) | (a ^* opp(b))})
      }
    }

    // In any ring the product of two non-zero elements is non-zero. 
    lazy val integralDomainLemma: Theorem = 
      forallI("a"::F,"b"::F){ case (a,b) => 
        implI(and(a !== z, b !== z,multInverseElement,multNeutralElement,multAssociative,
                  addOppositeElement,addNeutralElement,addAssociative,isDistributive)){ axioms => 
          val Seq(aNotZero,bNotZero,multInverseElement,multNeutralElement,multAssociative,
                  addOppositeElement,addNeutralElement,addAssociative,isDistributive) = andE(axioms) : Seq[Theorem]
          notI((a ^* b) === z) { case (hypothesis,_) => 
            val deriv = ((a ^* b) === z)             ==| andI(bNotZero,hypothesis)                                    |
            (((a ^* b) ^* inv(b)) === (z ^* inv(b))) ==| forallE(multAssociative)(a,b,inv(b))                  |
            ((a ^* (b ^* inv(b))) === (z ^* inv(b))) ==| andI(forallE(multInverseElement)(b),bNotZero)         |
            ((a ^* one) === (z ^* inv(b)))           ==| forallE(multNeutralElement)(a)                        |
            (a === (z ^* inv(b)))                    ==| forallE(implE(zeroDivisorLemma)(g => axioms))(inv(b)) |
            (a === z)                                ==| aNotZero     |
            ((a !== z) && (a === z))                
            andI(deriv,hypothesis)
          }
        }
      }
    // a+c = b+c ==> a = b
    lazy val cancellationLemma: Theorem = 
      forallI("a"::F,"b"::F,"c"::F){ case (a,b,c) => 
        implI(and(((a ^+ c) === (b ^+ c)),addAssociative,addOppositeElement,addNeutralElement)){ axioms => 
          val Seq(hypothesis,addAssociative,addOppositeElement,addNeutralElement) = andE(axioms) : Seq[Theorem]
          ((a ^+ c) === (b ^+ c)) ==| hypothesis |
          (((a ^+ c) ^+ opp(c)) === ((b ^+ c) ^+ opp(c))) ==| andI(forallE(addAssociative)(a,c,opp(c)),
                                                                   forallE(addAssociative)(b,c,opp(c))) |
          ((a ^+ (c ^+ opp(c))) === (b ^+ (c ^+ opp(c)))) ==| forallE(addOppositeElement)(c)            |
          ((a ^+ z) === (b ^+ z))                         ==| andI(forallE(addNeutralElement)(a),
                                                                   forallE(addNeutralElement)(b))       |
          (a === b)  
        }
      }

    //In a field (xy)^{-1} = (y)^{-1} (x)^{-1} for non-zero x,y
    lazy val inverseOfMult: Theorem =
      forallI("a"::F,"b"::F){ case (a,b) => 
        implI(and(multInverseElement,multNeutralElement,multAssociative,
                  addOppositeElement,addNeutralElement,addAssociative,isDistributive,
                  a !== z, b !== z)){ axioms =>
        val Seq(multInverseElement,multNeutralElement,multAssociative,
                addOppositeElement,addNeutralElement,addAssociative,isDistributive,
                aNotZero,bNotZero) = andE(axioms) : Seq[Theorem]
        val deduction = 
          ((a ^* b) ^* (inv(b) ^* inv(a))) ==| forallE(multAssociative)(a,b,(inv(b) ^* inv(a))) |
          (a ^* (b ^* (inv(b) ^* inv(a)))) ==| forallE(multAssociative)(b,inv(b),inv(a))        |
          (a ^* ((b ^* inv(b)) ^* inv(a))) ==| andI(forallE(multInverseElement)(b),bNotZero)    |                   
          (a ^* (one ^* inv(a)))           ==| forallE(multNeutralElement)(inv(a))              |
          (a ^* inv(a))                    ==| andI(forallE(multInverseElement)(a),aNotZero)    |
          one
          
        val symDeduction = 
          ((inv(b) ^* inv(a)) ^* (a ^* b)) ==| forallE(multAssociative)((inv(b) ^* inv(a)),a,b) |
          (((inv(b) ^* inv(a)) ^* a) ^* b) ==| forallE(multAssociative)(inv(b),inv(a),a)        |
          ((inv(b) ^* (inv(a) ^* a)) ^* b) ==| andI(forallE(multInverseElement)(a),aNotZero)    |
          ((inv(b) ^* one) ^* b)           ==| forallE(multNeutralElement)(inv(b))              |
          (inv(b) ^* b)                    ==| andI(forallE(multInverseElement)(b),bNotZero)    |
          one
        
        val implication = forallE(implE(uniqueMultInverseLemma)(g => axioms))((a ^* b), inv(a ^* b), (inv(b) ^* inv(a)))
        val assumption = andI(forallE(multInverseElement)((a ^* b)),deduction,symDeduction)
        //i need a theorem that says that the product of two non-zero is non-zero
        inv(a ^* b) ==| andI(assumption, implication,implE(forallE(integralDomainLemma)(a,b))(g => andI(axioms,aNotZero,bNotZero))) |
        inv(b) ^* inv(a)    
      }
    }

    // z !== opp(one)
    lazy val zeroNotMinusOne: Theorem = 
      implI(and(zeroNotOne,addOppositeElement,addNeutralElement,addAssociative)){ axioms =>
      val Seq(zeroNotOne,addOppositeElement,addNeutralElement,addAssociative) = andE(axioms) : Seq[Theorem]
      notI(opp(one) === z) { case (hypothesis,_) => 
        val deriv = 
          (opp(one) === z)                   ==| andI(hypothesis,zeroNotOne)      |
          ((opp(one) ^+ one) === (z ^+ one)) ==| forallE(addOppositeElement)(one) |
          (z === (z ^+ one))                 ==| forallE(addNeutralElement)(one)  |
          (z === one)                          
        andI(deriv,hypothesis,zeroNotOne)
      }
    }

    //In a ring inv(-1) = -1
    lazy val inverseOfMinusOne: Theorem = 
      implI(and(zeroNotOne,addOppositeElement,addNeutralElement,addAssociative,isDistributive,
          multInverseElement,multNeutralElement,multAssociative)){ axioms =>
        val Seq(zeroNotOne,addOppositeElement,addNeutralElement,addAssociative,isDistributive,
                multInverseElement,multNeutralElement,multAssociative) = andE(axioms) : Seq[Theorem]
          val minus1IsInverse = 
            (opp(one) ^* opp(one)) ==| forallE(implE(oppositeOfMultLemma)(g => axioms))(one,opp(one)) |
            opp(one ^* opp(one))   ==| forallE(multNeutralElement)(opp(one))                           |
            opp(opp(one))          ==| forallE(implE(oppositeInvolutionLemma)(g => axioms))(one)         |
            one
          val implication = forallE(implE(uniqueMultInverseLemma)(g => axioms))(opp(one),inv(opp(one)),opp(one))
          val assumption = andI(forallE(multInverseElement)(opp(one)),minus1IsInverse,minus1IsInverse)
          
          inv(opp(one)) ==| andI(implication, assumption,implE(zeroNotMinusOne)(g => axioms)) | opp(one)
      }
    

    //In a ring -(x)^{-1} = (-x)^{-1} 
    lazy val oppositeofInverseLemma: Theorem =
      forallI("x"::F){ case (x) => 
        implI(and(x !== z,addOppositeElement,addNeutralElement,addAssociative,isDistributive,
                multInverseElement,multNeutralElement,multAssociative)){ axioms =>
        val Seq(xNotZero,addOppositeElement,addNeutralElement,addAssociative,isDistributive,
                multInverseElement,multNeutralElement,multAssociative) = andE(axioms) : Seq[Theorem]
        
        
          inv(opp(x))               ==| forallE(multNeutralElement)(x)                               |
          inv(opp(one ^* x))        ==| forallE(implE(oppositeOfMultLemma)(g => axioms))(one, x)     |
          inv(opp(one) ^* x)        ==| implE(forallE(inverseOfMult)(opp(one),x))(g => andI(axioms,
                                                          implE(zeroNotMinusOne)(g => axioms)))       |
          (inv(x) ^* inv(opp(one))) ==| implE(inverseOfMinusOne)(g => axioms)                   |
          (inv(x) ^* opp(one))      ==| forallE(implE(oppositeOfMultLemma)(g => axioms))(inv(x),one) |
          opp(inv(x) ^* one)        ==| forallE(multNeutralElement)(inv(x))                          |
          opp(inv(x))
        }
      }

    /*
    * Theorems for the exponentiation
    */
    lazy val exp1Lemma: Theorem = 
    forallI("h" :: F){ case (h) => 
      implI(multNeutralElement){ axiom => 
        def property(n: Expr) = {
          ((h ^^ (n + E(BigInt(1)))) === ((h ^^ n) ^* h))
        }  

        naturalInduction(property _, E(BigInt(0)), (g: Goal) => g.by(
          (h ^^ (E(BigInt(0)) + E(BigInt(1)))) ==| axiom |
          (h)                                  ==| axiom |
          ((h ^^ (E(BigInt(0)))) ^* h) 
        )) { case (ihs, goal) =>
          val n = ihs.variable
          (h ^^ ((n + E(BigInt(1))) + E(BigInt(1)))) ==| ihs.variableGreaterThanBase |
          ((h ^^ (((n + E(BigInt(1))) + E(BigInt(1))) - E(BigInt(1)))) ^* h) ==| plusAssociativity(IntegerType) |
          ((h ^^ ((n + E(BigInt(1))) + (E(BigInt(1)) - E(BigInt(1))))) ^* h) ==| trivial |
          ((h ^^ ((n + E(BigInt(1))) + (E(BigInt(1)) - E(BigInt(1))))) ^* h)
          
        }
      }
    }  
    // h^(n+1) = h^n * h
    lazy val exp1Theorem: Theorem = prove(
      forall("h" :: F, "n" :: IntegerType){ case (h,n) => 
        (multNeutralElement && (n >= E(BigInt(0)))) ==> ((h ^^ (n + E(BigInt(1)))) === ((h ^^ n) ^* h))
      }, exp1Lemma
    )

    lazy val exp2Lemma: Theorem =
      forallI("i":: IntegerType,"h" :: F){ case (i,h) => 
        implI(and(i >= E(BigInt(0)), multNeutralElement,
                  multAssociative)){ case axioms =>
          val Seq(iNat,multNeutral,multAssoc) = andE(axioms): Seq[Theorem]
          def property(j: Expr) = {
            (((h ^^ i) ^* (h ^^ j)) === (h ^^ (i+j)))
          }  
          naturalInduction(property _, E(BigInt(0)), (g: Goal) => g.by(
            ((h ^^ i) ^* (h ^^ (E(BigInt(0))))) ==| trivial |
            ((h ^^ i) ^* one) ==| forallE(multNeutral)(h ^^ i) |  
            (h ^^ i) ==| trivial |
            (h ^^ (i + E(BigInt(0)))))
          ) { case (ihs, goal) =>
            val n = ihs.variable
              ((h ^^ i) ^* (h ^^ (n+E(BigInt(1))))) ==| ihs.variableGreaterThanBase |
              ((h ^^ i) ^* ((h ^^ n) ^* h))         ==| andI(forallE(multAssoc)(h^^i,h^^n,h),
                                                          ihs.propertyForVar) |
              ((h ^^ (i+n)) ^* h)                   ==| implE(forallE(exp1Theorem)(h,i+n))(g => 
                                                              andI(multNeutral,ihs.variableGreaterThanBase,iNat)) |
              (h ^^ (i+n+E(BigInt(1))))
            
          }      
        }
      }
    // h^(i+j) = h^i * h^j
    lazy val exp2Theorem: Theorem = prove(
      forall("h" :: F, "i" :: IntegerType, "j" :: IntegerType){ case (h,i,j) => 
        (i >= E(BigInt(0)) && j >= E(BigInt(0)) && multNeutralElement && multAssociative) ==>
          ((((h ^^ i) ^* (h ^^ j)) === (h ^^ (i+j))))
      }, exp2Lemma
    )
  
    /*
    * Theorems derived from the exclusion of characteristic 2 and 3
    */

    // If 2x = 0 then x = 0
    lazy val doubleXZeroLemma: Theorem =
      forallI("x"::F){ case (x) => 
        implI(and(double(x) === z,addNeutralElement,addOppositeElement,addAssociative,
                  multInverseElement,isDistributive,notCharacteristic2)){ axioms =>
          val Seq(doubleXZero,addNeutralElement,addOppositeElement,addAssociative,
                  multInverseElement,isDistributive,notCharacteristic2) = andE(axioms) : Seq[Theorem]
          notI(!(x === z)){ case (hypothesis,_) => 
            val deriv =
              (one ^+ one)                     ==| implE(forallE(multInverseElement)(x))(g => hypothesis)|
              ((x ^* inv(x)) ^+ (x ^* inv(x))) ==| forallE(isDistributive)(x,x,inv(x))                   |
              ((x ^+ x) ^* inv(x))             ==| doubleXZero                                           |
              (z ^* inv(x))                    ==| forallE(implE(zeroDivisorLemma)(g => axioms))(inv(x)) |
              z
            andI(hypothesis,deriv,notCharacteristic2)
          }
        }
      }

}