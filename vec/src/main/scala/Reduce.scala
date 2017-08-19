import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object Reduce{
  import SparsePolynomial._
  import List._
  import Field._

  //-----------------------------Reducing SHNF----------------------------------------------------
  val c = T(cons)(F) 
  val vars = c(E(BigInt(1)),
               c(E(BigInt(2)),
                  c(E(BigInt(3)),
                    c(E(BigInt(4)),
                      c(E(BigInt(5)),
                        c(E(BigInt(6)),
                          T(nil)(IntegerType)()))))))
  val x0ID = FreshIdentifier("x0"); 
  val x1ID = FreshIdentifier("x1"); 
  val x2ID = FreshIdentifier("x2"); 
  val y0ID = FreshIdentifier("y0"); 
  val y1ID = FreshIdentifier("y1"); 
  val y2ID = FreshIdentifier("y2");

  val y0: Expr = Variable(y0ID,F,Set())
  val y1: Expr = Variable(y1ID,F,Set())
  val y2: Expr = Variable(y2ID,F,Set())

  val x0: Expr = Variable(x0ID,F,Set())
  val x1: Expr = Variable(x1ID,F,Set())
  val x2: Expr = Variable(x2ID,F,Set())

  val vals: Expr = c(y0,c(y1,c(y2,c(x0,c(x1,c(x2,T(nil)(F)()))))))

  val xs = c(x0,c(x1,c(x2,T(nil)(F)())))
  val ys = c(y0,c(y1,c(y2,T(nil)(F)())))
  val aID = FreshIdentifier("a"); 
  val bID = FreshIdentifier("b");
  val A: Expr = Variable(aID,F,Set())
  val B: Expr = Variable(bID,F,Set())
  val theta: Expr =
    POP(E(BigInt(3)),
      POW(
        POW(constshf(one),E(BigInt(2)),constshf(A)),
        E(BigInt(1)),
        constshf(B)
      )
    )


  // shnf theta(a)
  // evalh(theta,vals) = x0^3 + (a*x0^2) + x0
  // evalh(theta,vals.tail) = x1^3 + (a*x1^2) + x1
  // evalh(theta,vals.tail.tail) = x2^3 + (a*x2) + x2
  // theorems on ecp...

  //j is restricted to 0,1,2
  val splitID = FreshIdentifier("split")
  val splitFunction = mkFunDef(splitID)() { case Seq() => 
    val args: Seq[ValDef] = Seq("h" :: shf,"j" :: IntegerType, "k" :: IntegerType)
    val retType: Type = TupleType(Seq(shf,shf))
    val body: Seq[Variable] => Expr = { case Seq(h,j,k) =>
      if_ (h.isInstOf(constshf) || j < k) {
        E(h,constshf(z))
      } else_ { if_ (h.isInstOf(POP)) { // j >= k
        val i = h.asInstOf(POP).getField(vi)
        val p = h.asInstOf(POP).getField(pshf)
        val tupl = E(splitID)(p,j,k+i); 
        val p0 = tupl._1; 
        val p1 = tupl._2
        E(pop(i,p0),pop(i,p1))
      } else_ { //POW 
        val i = h.asInstOf(POW).getField(vi)
        val p = h.asInstOf(POW).getField(pshf)
        val q = h.asInstOf(POW).getField(qshf)
        val ptupl = E(splitID)(p,j,k)             
        val p0 = ptupl._1
        val p1 = ptupl._2
        val qtupl = E(splitID)(q,j,k+E(BigInt(1))); 
        val q0 = qtupl._1 
        val q1 = qtupl._2
        if_ (j === k) {
          if_ (i % E(BigInt(2)) === E(BigInt(0))) {
            E(normadd(normmul(normexpt(theta,i / E(BigInt(2))),p0),pop(E(BigInt(1)),q0)),
              normadd(normmul(normexpt(theta,i / E(BigInt(2))),p1),pop(E(BigInt(1)),q1)))
          } else_ { //odd i
            E(normadd(normmul(normexpt(theta,(i+E(BigInt(1))) / E(BigInt(2))),p1),pop(E(BigInt(1)),q0)),
              normadd(normmul(normexpt(theta,(i-E(BigInt(1))) / E(BigInt(2))),p0),pop(E(BigInt(1)),q1)))
          }
        } else_ {
          E(pow(p0,i,q0),pow(p1,i,q1))
        }
      }
    }}
    (args, retType, body)
  }   

  val split = E(splitID)

  val rewriteID = FreshIdentifier("rewrite")
  val rewriteFunction = mkFunDef(rewriteID)() { case Seq() => 
    val args: Seq[ValDef] = Seq("h" :: shf,"j" :: IntegerType)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(h,j) =>
      val tupl = split(h,j,E(BigInt(0)))
      val h0 = tupl._1
      val h1 = tupl._2
      normadd(h0,normmul(h1,norm(variable(j))))
    }
    (args, retType, body)
  }    

  val rewrite = E(rewriteID)
  // j >= 2 && shnf h && r = rewrite(h,j) => shnf r && evalh(r,vals) = evalh(h,p) 

  //reduce successively rewrites powers of Y0, Y1, and Y2:
  val reduceID = FreshIdentifier("reduce")
  val reduceFunction = mkFunDef(reduceID)() { case Seq() => 
    val args: Seq[ValDef] = Seq("p" :: polex)
    val retType: Type = shf
    val body: Seq[Variable] => Expr = { case Seq(p) =>
      rewrite(rewrite(rewrite(norm(p),E(BigInt(0))),E(BigInt(1))),E(BigInt(2)))
    }
    (args, retType, body)
  }    

}