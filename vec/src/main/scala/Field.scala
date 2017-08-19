import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

object Field { 
  /*
    A non trivial field has elements different from zero.
    We can further assume the existence of a nonzero element called one.
    Any other element is of type notZeroOne.

    abstract class Element()
    final case class Zero() extends Element
    final case class One() extends Element()
    final case class notZeroOne() extends Element()

    The current implementation of Inox does not support inheritance between 
    abstract members. See: "Modelling a class hierarchy in Inox" on SO.
  */

  val elementID = FreshIdentifier("element")
  val zeroID = FreshIdentifier("zero")
  val oneID = FreshIdentifier("one")
  val notZeroOneID = FreshIdentifier("notZeroOne")

  val elementADT = mkSort(elementID)()(Seq(zeroID, oneID, notZeroOneID))
  val zeroADT = mkConstructor(zeroID)()(Some(elementID)) {_ => Seq()}
  val oneADT = mkConstructor(oneID)()(Some(elementID)) {_ => Seq()}
  val notZeroOneADT = mkConstructor(notZeroOneID)()(Some(elementID)) {_ => Seq()}

  /*
    Shorthands for field elements
  */
  val F = T(elementID)()
  val z = T(zeroID)()()
  val one = T(oneID)()()
  def nonZero(e: Expr): Expr = e.isInstOf(T(oneID)()) || e.isInstOf(T(notZeroOneID)())

  /*
    A field has an addition an a multiplication operation. 
    Operations opposite, inverse  and exponential can be derived.
  */

  val addID = FreshIdentifier("add");      val multID = FreshIdentifier("mult")  
  val oppositeID = FreshIdentifier("opp"); val inverseID = FreshIdentifier("inv")  
  val powerID = FreshIdentifier("pow")

  //Current version of Inox does not require set of flags anymore.
  val addFunction: Expr = Variable(addID, (F, F) =>: F,Set())
  val multFunction: Expr = Variable(multID, (F, F) =>: F,Set())
  val oppositeFunction: Expr = Variable(oppositeID, (F) =>: F,Set())
  val inverseFunction: Expr = Variable(inverseID, (F) =>: F,Set())
  val powerFunction = mkFunDef(powerID)() { case Seq() => 
    val args: Seq[ValDef] = Seq("x" :: F, "n" :: IntegerType)
    val returnType: Type = F
    val body: Seq[Variable] => Expr = { case Seq(x,n) =>
      if_ (n <= E(BigInt(0))) {
        one
      } else_ {
        multFunction(E(powerID)(x,n - E(BigInt(1))),x) 
      }
    }
    (args,returnType,body)
  }

  /*
    Introduction of infix notation. 
    We write ^operand to avoid ambiguity with the Inox DSL
    We have to introduce the exponentiation.
  */
  implicit class ExprOperands(private val lhs: Expr) extends AnyVal{
    def ^+(rhs: Expr): Expr = addFunction(lhs, rhs)
    def ^-(rhs: Expr): Expr = addFunction(lhs,opp(rhs))
    def ^*(rhs: Expr): Expr = multFunction(lhs, rhs)
    def ^/(rhs: Expr): Expr = multFunction(lhs,inv(rhs))
    def ^^(rhs: Expr): Expr = powerFunction(lhs,rhs)
  }
  def opp(e: Expr): Expr = oppositeFunction(e)
  def inv(e: Expr): Expr = inverseFunction(e)
  /*
    Shorthands for formulas of addition on curves.
    By now we see no reason to extend this to an scalar multiplication.
  */
  def double(e: Expr): Expr = e ^+ e
  def triple(e: Expr): Expr = e ^+ e ^+ e
  
}
  

  


