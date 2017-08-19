import inox._
import inox.trees.{forall => _, _}
import inox.trees.dsl._

import welder._

object Register{
  import Curve._
  import Field._
  import SparsePolynomial._
  import List._
  import Reduce._
  //---------------------------Registering elements-----------------------------------

  val listADTs = Seq(listADT, nilADT, consADT)
  val fieldADTs = Seq(elementADT, zeroADT, oneADT, notZeroOneADT)
  val curveADTs = Seq(affinePointADT, infiniteADT, finiteADT)
  val polynomialADTs = Seq(polexADT, constADT, varADT, addADT, mulADT, negADT, expADT)
  val shfADTs = Seq(shfADT, constshfADT, POP_ADT, POW_ADT)

  val fieldOperations = Seq(powerFunction)
  val listOperations = Seq(dropFunction, atFunction)
  val curveOperations = Seq(onCurveFunction, addCurveFunction, oppCurveFunction)
  val shfFunctions = Seq(shfCountFunction, polexpFunction, shfpFunction, shfnormpFunction,
                         evalhFunction, evalpFunction)
  val normFunctions = Seq(normpopFunction, normpowFunction, normFunction, normExptFunction,
                          normNegFunction)
  val normaddFunctions = Seq(normAddFunction)
  val normmulFunctions = Seq(normMulFunction, normMul1Function, normMul2Function, normMul3Function)
  val rewritingFunctions = Seq(splitFunction, rewriteFunction,reduceFunction)

  val symbols = NoSymbols
    .withADTs(listADTs ++  fieldADTs ++ curveADTs ++ polynomialADTs ++ shfADTs)
    .withFunctions(fieldOperations ++ listOperations ++ curveOperations ++
                   shfFunctions ++ normFunctions ++ normaddFunctions ++
                   normmulFunctions ++ rewritingFunctions)
  //println(symbols) 
  //println(symbols.explainTyping(addConstPopFunction.fullBody)(PrinterOptions()))
  //println(symbols.ensureWellFormed)
  //println(theory.symbols.explainTyping(vals)(PrinterOptions()))

  val program = InoxProgram(Context.empty, symbols)
  val theory = theoryOf(program)
}