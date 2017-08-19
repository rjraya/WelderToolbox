import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

// Theory of sparse Horner normal form for integer polynomials
object SparsePolynomial{
  import Field._
  import List._

  val fc = FreshIdentifier("field_const");       val vi = FreshIdentifier("variable_index")
  val fa = FreshIdentifier("first_addend");      val sa = FreshIdentifier("second_addend")
  val ff = FreshIdentifier("first_factor");      val sf = FreshIdentifier("second_factor")
  val oa = FreshIdentifier("opposite_argument"); val b  = FreshIdentifier("base")
  val e  = FreshIdentifier("exponent")

  //-----------------------------Polynomial term----------------------------------------------------

  val polexID = FreshIdentifier("polex")
  val variableID = FreshIdentifier("var"); val constID = FreshIdentifier("const")
  val addID = FreshIdentifier("add");      val mulID = FreshIdentifier("mul")
  val negID = FreshIdentifier("neg");      val expID = FreshIdentifier("exp")

  val polexADT = mkSort(polexID)()(Seq(negID,constID,variableID,addID,mulID,expID))  
  val constADT = mkConstructor(constID)()(Some(polexID)){ case Seq() => Seq(ValDef(fc, F)) }
  val varADT = mkConstructor(variableID)()(Some(polexID)){ case Seq() => Seq(ValDef(vi, IntegerType))}
  val addADT = mkConstructor(addID)()(Some(polexID)){ case Seq() => 
    Seq(ValDef(fa, T(polexID)()),ValDef(sa, T(polexID)()))
  }
  val mulADT = mkConstructor(mulID)()(Some(polexID)){ case Seq() => 
    Seq(ValDef(ff, T(polexID)()),ValDef(sf, T(polexID)()))
  }
  val negADT = mkConstructor(negID)()(Some(polexID)){ case Seq() => 
    Seq(ValDef(oa, T(polexID)())) 
  }
  val expADT = mkConstructor(expID)()(Some(polexID)){ case Seq() => 
    Seq(ValDef(b, T(polexID)()),ValDef(e, IntegerType)) 
  }

  val polex = T(polexID)()
  val const = T(constID)(); val variable = T(variableID)()
  val add = T(addID)();     val mul = T(mulID)()
  val neg = T(negID)();     val exp = T(expID)()

  // This function test if integer parameters are natural.
  val polexpID = FreshIdentifier("polexp")
  val polexpFunction: FunDef = mkFunDef(polexpID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("p" :: polex)
    val retType: Type = BooleanType
    val body: Seq[Variable] => Expr = { case Seq(p) => 
      if_ (p.isInstOf(const) || p.isInstOf(add) || p.isInstOf(mul) || p.isInstOf(neg)){
        BooleanLiteral(true)
      } else_ {
        if_ (p.isInstOf(variable)) {
          p.asInstOf(variable).getField(vi) >= E(BigInt(0))
        } else_ { //exp 
          p.asInstOf(exp).getField(e) >= E(BigInt(0))
        }
      }
    }
    (args, retType, body)
  }


  //-----------------------------Sparse Horner Form---------------------------------------------------------

  val pshf = FreshIdentifier("pshf");  val qshf = FreshIdentifier("qshf")
  val shfID = FreshIdentifier("shf");  val constshfID = FreshIdentifier("constshf")
  val POP_ID = FreshIdentifier("POP"); val POW_ID = FreshIdentifier("POW")

  val shfADT = mkSort(shfID)()(Seq(constshfID,POP_ID,POW_ID))  
  val constshfADT = mkConstructor(constshfID)()(Some(shfID)){ case Seq() => Seq(ValDef(fc,F)) }
  val POP_ADT = mkConstructor(POP_ID)()(Some(shfID)){ case Seq() => 
    Seq(ValDef(vi,IntegerType),ValDef(pshf, T(shfID)())) 
  }
  val POW_ADT = mkConstructor(POW_ID)()(Some(shfID)){ case Seq() => 
    Seq(ValDef(pshf,T(shfID)()),ValDef(vi,IntegerType),ValDef(qshf, T(shfID)()))
  }

  val shf = T(shfID)();  val constshf = T(constshfID)() 
  val POP = T(POP_ID)(); val POW = T(POW_ID)()

  // Function to count the number of elements of a shf.
  val shfCountID = FreshIdentifier("shfCount")
  val shfCountFunction: FunDef = mkFunDef(shfCountID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("p" :: shf)
    val retType: Type = IntegerType
    val body: Seq[Variable] => Expr = { case Seq(p) => 
      if_ (p.isInstOf(constshf)){
        E(BigInt(1))
      } else_ {
        if_ (p.isInstOf(POP)) {
          E(BigInt(2)) + E(shfCountID)(p.asInstOf(POP).getField(pshf))
        } else_ {// POW
          E(BigInt(2)) + 
          E(shfCountID)(p.asInstOf(POW).getField(pshf)) + 
          E(shfCountID)(p.asInstOf(POW).getField(qshf))
        } 
      }
    }
    (args, retType, body)
  }

  // This function test if integer parameters are natural.
  val shfpID = FreshIdentifier("shfp")
  val shfpFunction: FunDef = mkFunDef(shfpID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("p" :: shf)
    val retType: Type = BooleanType
    val body: Seq[Variable] => Expr = { case Seq(p) => 
      if_ (p.isInstOf(constshf)){
        BooleanLiteral(true)
      } else_ {
        if_ (p.isInstOf(POP)) {
          p.asInstOf(POP).getField(vi) >= E(BigInt(0)) &&
          E(shfpID)(p.asInstOf(POP).getField(pshf)) 
        } else_ {// POW
          p.asInstOf(POW).getField(vi) >= E(BigInt(0)) &&
          E(shfpID)(p.asInstOf(POW).getField(pshf)) &&
          E(shfpID)(p.asInstOf(POW).getField(qshf))
        } 
      }
    }
    (args, retType, body)
  }

  //--------------------------------Sparse normal form------------------------------------------

  val shfnormpID = FreshIdentifier("shfnormp")
  val shfnormpFunction: FunDef = mkFunDef(shfnormpID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("pol" :: shf)
    val retType: Type = BooleanType
    val body: Seq[Variable] => Expr = { case Seq(pol) => 
      if_ (pol.isInstOf(constshf)) {
        BooleanLiteral(true)
      } else_ { if_ (pol.isInstOf(POP)) {
        val i = pol.asInstOf(POP).getField(vi)
        val p = pol.asInstOf(POP).getField(pshf)
        (i > E(BigInt(0))) && E(shfnormpID)(p) && p.isInstOf(POW)
      } else_ { //POW
        val i = pol.asInstOf(POW).getField(vi)
        val p = pol.asInstOf(POW).getField(pshf)
        val q = pol.asInstOf(POW).getField(qshf)
        val form1 = {
          val r = p.asInstOf(POW).getField(qshf)
          r.isInstOf(constshf) && (r.asInstOf(constshf).getField(fc) === z)
        }  
        val form2 = {
          (p.asInstOf(constshf).getField(fc) === z)
        }
        (i > E(BigInt(0))) && E(shfnormpID)(p) && E(shfnormpID)(q) && 
          !(p.isInstOf(POW) && form1) && !(p.isInstOf(constshf) && form2)
      }}
    }

    (args, retType, body)
  }

  //---------------------------------Converting a Polynomial to SHNF------------------------------------------

  val normpopID = FreshIdentifier("normpop")
  val normpopFunction: FunDef = mkFunDef(normpopID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("i" :: IntegerType,"p" :: shf)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(i,p) => 
      if_ ( (i === E(BigInt(0))) || p.isInstOf(constshf) ) {
        p
      } else_ { if_ (p.isInstOf(POP)) {
        val j = p.asInstOf(POP).getField(vi) 
        val q = p.asInstOf(POP).getField(pshf)
        POP(i+j,q)
      } else_ { //POW
        POP(i,p)
      }}
    }

    (args, retType, body)
  }

  val normpowID = FreshIdentifier("pow")
  val normpowFunction: FunDef = mkFunDef(normpowID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("p" :: shf, "i" :: IntegerType, "q" :: shf)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(p,i,q) => 
      if_ (p.isInstOf(constshf) && (p.asInstOf(constshf).getField(fc) === z)) {
        E(normpopID)(E(BigInt(1)),q)
      } else_ { if_ (p.isInstOf(POW) && 
           (p.asInstOf(POW).getField(qshf).isInstOf(constshf)) && 
           (p.asInstOf(POW).getField(qshf).asInstOf(constshf).getField(fc) === z)) {
        val r = p.asInstOf(POW).getField(pshf)
        val j = p.asInstOf(POW).getField(vi) 
        POW(r,i+j,q)
      } else_ {//POW
        POW(p,i,q)
      }}
    }

    (args, retType, body) 
  }

  val shfCount = E(shfCountID)
  val shfp = E(shfpID)
  val shfnormp = E(shfnormpID)
  val pop = E(normpopID)
  val pow = E(normpowID)
  //---------------------------Evaluation of polex--------------------------------------------------
  
  val evalpID = FreshIdentifier("evalp")
  val evalpFunction: FunDef = mkFunDef(evalpID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("p" :: polex, "l" :: T(list)(F))
    val retType: Type = F
    val body: Seq[Variable] => Expr = { case Seq(p,l) => 
      if_ (p.isInstOf(const)) {
        p.asInstOf(const).getField(fc)
      } else_ { if_ (p.isInstOf(variable)) {
        val index = p.asInstOf(variable).getField(vi)
        at(F)(l,index)
      } else_ { if_ (p.isInstOf(add)) {
        val v1 = p.asInstOf(add).getField(fa)
        val v2 = p.asInstOf(add).getField(sa)
        E(evalpID)(v1,l) ^+ E(evalpID)(v2,l)
      } else_ { if_ (p.isInstOf(mul)) {
        val v1 = p.asInstOf(mul).getField(ff)
        val v2 = p.asInstOf(mul).getField(sf)
        E(evalpID)(v1,l) ^* E(evalpID)(v2,l)
      } else_ { if_ (p.isInstOf(neg)) {
        val v1 = p.asInstOf(neg).getField(oa)
        opp(E(evalpID)(v1,l))
      } else_{ //exp
        val v1 = p.asInstOf(exp).getField(b)
        val v2 = p.asInstOf(exp).getField(e)
        E(evalpID)(v1,l) ^^ v2
      }}}}} 
    }

    (args, retType, body)
  }

  val evalp = E(evalpID)

//---------------------------Evaluation of shf-----------------------------------------------------  
  
  val evalhID = FreshIdentifier("evalh")
  val evalhFunction: FunDef = mkFunDef(evalhID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("p" :: shf, "l" :: T(list)(F))
    val retType: Type = F
    val body: Seq[Variable] => Expr = { case Seq(p,l) => 
      if_ (p.isInstOf(constshf)) {
        p.asInstOf(constshf).getField(fc)
      } else_ { if_ (p.isInstOf(POP)) {
        val i = p.asInstOf(POP).getField(vi)
        val q = p.asInstOf(POP).getField(pshf)
        E(evalhID)(q,drop(F)(l,i))
      } else_ { 
        val firstpol = p.asInstOf(POW).getField(pshf)
        val i = p.asInstOf(POW).getField(vi)
        val secondpol = p.asInstOf(POW).getField(qshf)
        if_ (l.isInstOf(T(cons)(F))) {
          val h = l.asInstOf(T(cons)(F)).getField(head)
          val t = l.asInstOf(T(cons)(F)).getField(tail)
          ((h ^^ i) ^* E(evalhID)(firstpol,l)) ^+ E(evalhID)(secondpol,t)
        } else_ {
          E(evalhID)(secondpol,l)
        }
      }}}

    (args, retType, body)
  }  

  val evalh = E(evalhID)
  

//-----------------------------Syntactic sugar for previous functions-----------------------------

  // norm-add computes a normal representation of (+ a b),
  // given normal representations x and y of a and b.
  // this function is splitted into pieces in order to proof things
  val normAddID = FreshIdentifier("normadd")
  val normAddFunction: FunDef = mkFunDef(normAddID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("x" :: shf, "y" :: shf)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(x,y) => 
      if_ (x.isInstOf(constshf)) {
        if_ (y.isInstOf(constshf)) {
          constshf(x.asInstOf(constshf).getField(fc) ^+ 
                   y.asInstOf(constshf).getField(fc))
        } else_ { if_ (y.isInstOf(POP)) {
          val i = y.asInstOf(POP).getField(vi)
          val p = y.asInstOf(POP).getField(pshf)
          POP(i,E(normAddID)(x,p))
        } else_ { // POW
          val i = y.asInstOf(POW).getField(vi)
          val p = y.asInstOf(POW).getField(pshf)
          val q = y.asInstOf(POW).getField(qshf)
          POW(p,i,E(normAddID)(x,q))
        }}     
      } else_ { if_ (y.isInstOf(constshf)) {
        E(normAddID)(y,x)
      } else_ { if_ (x.isInstOf(POP)) {
        val i = x.asInstOf(POP).getField(vi)
        val p = x.asInstOf(POP).getField(pshf)
        if_ (y.isInstOf(POP)) {
          val j = y.asInstOf(POP).getField(vi)
          val q = y.asInstOf(POP).getField(pshf)
          if_ (i === j) {
            E(normpopID)(i,E(normAddID)(p,q))
          } else_ { if_ (i > j) {
            E(normpopID)(j,E(normAddID)(POP(i-j,p),q))
          } else_ { //i < j
            E(normpopID)(i,E(normAddID)(POP(j-i,q),p))
          }}
        } else_ { // p2.isInstOf(POW)
          val q = y.asInstOf(POW).getField(pshf)
          val r = y.asInstOf(POW).getField(qshf)
          val j = y.asInstOf(POW).getField(vi)
          if_ (i === E(BigInt(1))) {
            POW(q,j,E(normAddID)(r,p))
          } else_ { // i > 1
            POW(q,j,E(normAddID)(r,POP(i-E(BigInt(1)),p)))
          }
        }
      } else_ { if_ (y.isInstOf(POP)) {
        E(normAddID)(y,x)
      } else_ { // POW-POW
        val i = x.asInstOf(POW).getField(vi)
        val p = x.asInstOf(POW).getField(pshf)
        val q = x.asInstOf(POW).getField(qshf)
        val j = y.asInstOf(POW).getField(vi)
        val r = y.asInstOf(POW).getField(pshf)
        val s = y.asInstOf(POW).getField(qshf)
        if_ (i === j) {
          E(normpowID)(E(normAddID)(p,r), i, E(normAddID)(q,s))
        } else_ { if_ (i > j) {
          E(normpowID)(E(normAddID)(POW(p,i-j,constshf(z)),r), j, E(normAddID)(q,s))
        } else_ {
          E(normpowID)(E(normAddID)(POW(r,j-i,constshf(z)),p), i, E(normAddID)(s,q))
        }}
      }}}}
    }

    (args, retType, body)
  }

  val normNegID = FreshIdentifier("normneg")
  val normNegFunction: FunDef = mkFunDef(normNegID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("pol" :: shf)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(pol) => 
      if_ (pol.isInstOf(constshf)) {
        constshf(opp(pol.asInstOf(constshf).getField(fc)))
      } else_ { if_ (pol.isInstOf(POP)) {
        val i = pol.asInstOf(POP).getField(vi)
        val p = pol.asInstOf(POP).getField(pshf)
        POP(i,E(normNegID)(p))
      } else_ { // POW
        val i = pol.asInstOf(POW).getField(vi)
        val p = pol.asInstOf(POW).getField(pshf)
        val q = pol.asInstOf(POW).getField(qshf)
        POW(E(normNegID)(p),i,E(normNegID)(q))
      }}
    }

    (args, retType, body)
  }

  val normMulID = FreshIdentifier("normmul")
  val normMul1ID = FreshIdentifier("normMul1")
  val normMul2ID = FreshIdentifier("normMul2")
  val normMul3ID = FreshIdentifier("normMul3")

  val normMul1Function: FunDef = mkFunDef(normMul1ID)(){ case Seq() =>
    val args: Seq[ValDef] = Seq("x" :: shf, "y" :: shf)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(x,y) => 
      val i = x.asInstOf(POW).getField(vi)
      val p = x.asInstOf(POW).getField(pshf)
      val q = x.asInstOf(POW).getField(qshf)    
      val j = y.asInstOf(POW).getField(vi) 
      val r = y.asInstOf(POW).getField(pshf)    
      val s = y.asInstOf(POW).getField(qshf)
      val fterm = E(normpowID)(E(normMulID)(p,r),i+j,E(normMulID)(q,s))
      val sterm = E(normpowID)(E(normMulID)(p,E(normpopID)(E(BigInt(1)),s)),i,constshf(z))
      val tterm = E(normpowID)(E(normMulID)(r,E(normpopID)(E(BigInt(1)),q)),j,constshf(z))
      E(normAddID)(E(normAddID)(fterm,sterm),tterm)
    }

    (args, retType, body)
  }

  val normMul2Function: FunDef = mkFunDef(normMul2ID)(){ case Seq() =>
    val args: Seq[ValDef] = Seq("x" :: shf, "y" :: shf)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(x,y) =>
      val i = x.asInstOf(POP).getField(vi)
      val p = x.asInstOf(POP).getField(pshf)
      val q = y.asInstOf(POW).getField(pshf)
      val r = y.asInstOf(POW).getField(qshf)
      val j = y.asInstOf(POW).getField(vi)
      if_ (i === E(BigInt(1))) {
        E(normpowID)(E(normMulID)(x,q),j,E(normMulID)(p,r))
      } else_ { // i > 1
        E(normpowID)(E(normMulID)(x,q),j,E(normMulID)(POP(i-E(BigInt(1)),p),r))
      }
    }

    (args, retType, body)
  }

  val normMul3Function: FunDef = mkFunDef(normMul3ID)(){ case Seq() =>
    val args: Seq[ValDef] = Seq("x" :: shf, "y" :: shf)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(x,y) =>
      val i = x.asInstOf(POP).getField(vi)
      val p = x.asInstOf(POP).getField(pshf)
      val j = y.asInstOf(POP).getField(vi)
      val q = y.asInstOf(POP).getField(pshf)
      if_ (i === j) {
        E(normpopID)(i,E(normMulID)(p,q))
      } else_ { if_ (i > j) {
        E(normpopID)(j,E(normMulID)(POP(i-j,p),q))
      } else_ { //i < j
        E(normpopID)(i,E(normMulID)(POP(j-i,q),p))
      }}
    }

    (args, retType, body)
  }
 
  val normMulFunction: FunDef = mkFunDef(normMulID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("x" :: shf, "y" :: shf)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(x,y) => 
      if_ (x.isInstOf(constshf)) {
        if_ (y.isInstOf(constshf)) {
          constshf(x.asInstOf(constshf).getField(fc) ^*
                   y.asInstOf(constshf).getField(fc))
        } else_ { if_ (y.isInstOf(POP)) {
          val i = y.asInstOf(POP).getField(vi)
          val p = y.asInstOf(POP).getField(pshf)
          E(normpopID)(i,E(normMulID)(x,p))
        } else_ { // POW
          val i = y.asInstOf(POW).getField(vi)
          val p = y.asInstOf(POW).getField(pshf)
          val q = y.asInstOf(POW).getField(qshf)
          E(normpowID)(E(normMulID)(x,p),i,E(normMulID)(x,q))
        }}     
      } else_ { if_ (y.isInstOf(constshf)) {
        E(normMulID)(y,x)
      } else_ { if_ (x.isInstOf(POP)) {
        if_ (y.isInstOf(POP)) {
          E(normMul3ID)(x,y)
        } else_ { // p2.isInstOf(POW)
          E(normMul2ID)(x,y)
        }
      } else_ { if_ (y.isInstOf(POP)) {
        E(normMulID)(y,x)
      } else_ { // POW-POW
        E(normMul1ID)(x,y)
      }}}}
    }

    (args, retType, body)
  }  

  val normExptID = FreshIdentifier("normexpt")
  val normExptFunction: FunDef = mkFunDef(normExptID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("x" :: shf,"k" :: IntegerType)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(x,k) => 
      if_ (k <= E(BigInt(0))) {
        constshf(one)
      } else_ {
        E(normMulID)(x,E(normExptID)(x,k-E(BigInt(1))))
      }
    }

    (args, retType, body)
  }    

  //the index of a variable is given when constructed
  val normID = FreshIdentifier("norm")
  val normFunction: FunDef = mkFunDef(normID)(){ case Seq() => 
    val args: Seq[ValDef] = Seq("x" :: polex)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(x) => 
      if_ (x.isInstOf(const)) {
        val fieldConstant = x.asInstOf(const).getField(fc)
        constshf(fieldConstant)
      } else_ { if_ (x.isInstOf(variable)) { 
        val index = x.asInstOf(variable).getField(vi)
        E(normpopID)(index,POW(constshf(one),E(BigInt(1)),constshf(z)))
      } else_ { if_ (x.isInstOf(add)) {
        val faddend = x.asInstOf(add).getField(fa)
        val saddend = x.asInstOf(add).getField(sa)
        E(normAddID)(E(normID)(faddend), E(normID)(saddend))
      } else_ { if_ (x.isInstOf(mul)) {
        val ffactor = x.asInstOf(mul).getField(ff)
        val sfactor = x.asInstOf(mul).getField(sf)
        E(normMulID)(E(normID)(ffactor),E(normID)(sfactor))
      } else_ { if_ (x.isInstOf(neg)) {
        val oargument = x.asInstOf(neg).getField(oa)
        E(normNegID)(E(normID)(x))
      } else_ { //expt
        val exptBase = x.asInstOf(exp).getField(b)
        val exptExponent = x.asInstOf(exp).getField(e)
        E(normExptID)(E(normID)(exptBase),exptExponent)
      }}}}}
    }

    (args, retType, body)
  }  

  val normadd = E(normAddID)
  val normneg = E(normNegID)
  val normmul = E(normMulID)
  val normexpt = E(normExptID)
  val norm = E(normID)
}  