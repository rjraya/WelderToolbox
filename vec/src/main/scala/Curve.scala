import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object Curve{
  import Field._
  //-------------------------------Definitions-----------------------------------------------
  val affinePoint = FreshIdentifier("affinePoint")
  val infinitePoint = FreshIdentifier("infinitePoint")
  val finitePoint = FreshIdentifier("finitePoint")
  val first = FreshIdentifier("first")
  val second = FreshIdentifier("second")

  /*
    abstract class AffinePoint()
    final case class InfinitePoint() extends AffinePoint
    final case class FinitePoint(first: Field, second: Field) extends AffinePoint
  */
  val affinePointADT = mkSort(affinePoint)("F")(Seq(infinitePoint,finitePoint))
  val infiniteADT = mkConstructor(infinitePoint)("F")(Some(affinePoint))(_ => Seq())
  val finiteADT = mkConstructor(finitePoint)("F")(Some(affinePoint)){ case Seq(fT) =>
    Seq(ValDef(first, fT), ValDef(second, fT))
  }
  //--------------------Type for elements of the elliptic curve--------------------------------
  val affine = T(affinePoint)(F)
  val infinite = T(infinitePoint)(F)
  val finite = T(finitePoint)(F)

  //---------------------------------Functions definitions--------------------------------------

  val onCurveID = FreshIdentifier("onCurve")
  val addCurveID = FreshIdentifier("add")
  val oppCurveID = FreshIdentifier("opp")

  val onCurveFunction = mkFunDef(onCurveID)() { case Seq() => 
    val args: Seq[ValDef] = Seq("p" :: affine, "a" :: F, "b" :: F)
    val retType: Type = BooleanType
    val body: Seq[Variable] => Expr = { case Seq(p,a,b) =>
      if_ (p.isInstOf(finite)){
        val x: Expr = p.asInstOf(finite).getField(first)
        val y: Expr = p.asInstOf(finite).getField(second)
        (y ^* y) === {(x ^* x ^* x) ^+ (a ^* x) ^+ b}
      } else_ {
        BooleanLiteral(true)
      }
    }
    (args, retType, body)
  }
  
  /*
   * For two points in curve return its addition. 
   * Furthermore, if one of the two points is not on curve then return infinite.
  */ 
  val addCurveFunction = mkFunDef(addCurveID)() { case Seq() => 
    val args: Seq[ValDef] = Seq("p1" :: affine, "p2" :: affine, "a" :: F, "b" :: F)
    val retType: Type = affine
    val body: Seq[Variable] => Expr = { case Seq(p1,p2,a,b) =>

      if_ (not(E(onCurveID)(p1, a, b)) || not(E(onCurveID)(p2, a, b))) {infinite()} else_ {
      if_(p1.isInstOf(infinite)){p2} else_ {
      if_(p2.isInstOf(infinite)){p1} else_ {         
        val p3 = p1.asInstOf(finite); val x1 = p3.getField(first); val y1 = p3.getField(second);
        val p4 = p2.asInstOf(finite); val x2 = p4.getField(first); val y2 = p4.getField(second);
         
        if_ (x1 === x2){
          if_ (y1 === y2 && !y1.isInstOf(T(zeroID)())){
            val lambda = (triple(x1 ^* x1) ^+ a) ^/ (double(y1))
            val x = (lambda ^* lambda) ^- (double(x1))
            val y = (lambda ^* (x1 ^- x)) ^- y1
            finite(x,y)
          } else_ {
            infinite()
          }
        } else_ {
          val lambda = (y2 ^- y1) ^/ (x2 ^- x1) 
          val x = (lambda ^* lambda) ^- x1 ^- x2
          val y = (lambda ^* (x1 ^- x)) ^- y1
          finite(x,y)
        }
      }}}
    }
    (args, retType, body)
  }

  val oppCurveFunction = mkFunDef(oppCurveID)() { case Seq() => 
    val args: Seq[ValDef] = Seq("p" :: affine)
    val retType: Type = affine
    val body: Seq[Variable] => Expr = { case Seq(p) =>
      if_(p.isInstOf(finite)){
        val x = p.asInstOf(finite).getField(first)
        val y = p.asInstOf(finite).getField(second)
        finite(x,opp(y))
      } else_ {
        infinite()
      }
    }
    (args, retType, body)
  }

  //---------------------Helper functions for elliptic curve operations---------------
  def addCurve(p1: Expr, p2:Expr, a: Expr, b: Expr): Expr = E(addCurveID)(p1, p2, a, b)
  def onCurve(p: Expr, a: Expr, b: Expr): Expr = E(onCurveID)(p,a,b) 
  def oppCurve(p: Expr): Expr = E(oppCurveID)(p)
}