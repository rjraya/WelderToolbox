package welder

trait Tactics { self: Theory =>

  import program.trees._

  /*
    Introduce predicate induction on that will choose by itself the induction
    principle to use.

   */

  /* automatised theorems: countLemma, normalityLemma, dropLemma

    Example use:

    lazy val firstLemma: Theorem = {
      def property(l: Expr) = {
        forall("i" :: IntegerType, "j" :: IntegerType){ case (i,j) =>
          (i >= E(BigInt(0)) && j >= E(BigInt(0))) ==> (drop(F)(l,i+j) === drop(F)(drop(F)(l,j),i))
        }
      }
      induct(property _, "l" :: T(list)(F))
    }
   */
  def induct(property: Expr => Expr, valDef: ValDef): Attempt[Theorem] = {
    val tpe = valDef.tpe.asInstanceOf[ADTType]

    val cases: (StructuralInductionHypotheses, Goal) => Attempt[Witness] = { case (ihs,_) =>
      val hypothesis: Seq[Attempt[Theorem]] = for{
        v <- ihs.variables
        if v.tpe == tpe
      } yield ihs.hypothesis(v)

      Attempt.all(hypothesis) match {
        case Success(thm :: thms) => thm :: thms reduceLeft ((x, y) => andI(x, y))
        case _ => truth
      }
    }

    structuralInduction(property, valDef)(cases)
  }

  def natInduct(property: Expr => Expr, base: Expr, baseCase: Goal => Attempt[Witness]): Attempt[Theorem] = {
    val inductiveCase: (NaturalInductionHypotheses, Goal) => Attempt[Witness] = { case (ihs,_) =>
      andI(ihs.propertyForLessOrEqualToVar,
           ihs.variableGreaterThanBase,
           ihs.propertyForVar)
    }
    naturalInduction(property, base, baseCase)(inductiveCase)

  }

}

