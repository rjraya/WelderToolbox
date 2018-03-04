// Following book Term rewriting and all that

object TRS {

  type vname = (String,Int)

  abstract class Term{
    def print(): Unit
  }
  case class V(x: vname) extends Term{
    def print(): Unit ={
      println(x._1 + x._2)
    }
  }
  case class T(name: String,terms: List[Term]) extends Term {
    def print(): Unit ={
      println(name + (terms map (t => t.print)))
    }
  }

  type subst = List[(vname,Term)]

  // Checks if x is in the domain of s
  def indom(x: vname)(s: subst): Boolean = s exists{ case (y :vname,_ :Term) => x == y}

  // Apply substitution s to variable x. One case is undefined?
  def app(s: subst)(x: vname): Term = s match{
    case (y: vname,t)::tl => if (x == y) t else app(tl)(x)
  }

  // Extends notion of substitution to terms
  def lift(s: subst)(t: Term): Term =  t match{
    case v@V(x) => if (indom(x)(s)) app(s)(x) else v
    case T(f,ts) => T(f,ts map{p: Term => lift(s)(p)})
  }

  // Tests if x is a variable of t
  def occurs(x: vname)(t: Term): Boolean = t match{
    case V(y) => x == y
    case T(_,ts) => ts exists{ tm => occurs(x)(tm) }
  }

  class unifyException extends Exception

  def elim(x: vname,t: Term,l: List[(Term,Term)],s: subst): subst =
    if (occurs(x)(t)) throw new unifyException() else {
      val xt: Term => Term = lift(List((x,t)))
      val arg1: List[(Term,Term)] = l map {case (t1,t2) => (xt(t1),xt(t2))}
      val arg2: subst = (x,t) :: s map {case (y: vname,u: Term) => (y,xt(u))}
      solve(arg1,arg2)
    }

  // l unification problem to be solved
  // s already compute substitution
  def solve(l :List[(Term,Term)],s :subst): subst = l match {
    case Nil => s
    case (v@V(x),t) :: tl => if (v == t) solve(tl,s) else elim(x,t,tl,s)
    case (t,V(x)) :: tl => elim(x,t,tl,s)
    case (T(f,ts),T(g,us)) :: tl => if (f == g) solve( (ts zip us) ++ tl, s) else throw new unifyException()
  }

  def unify(t1: Term,t2: Term): subst = solve(List((t1,t2)),Nil)

  def matchs(l: List[(Term,Term)],s: subst): subst = l match {
    case Nil => s
    case (V(x),t) :: tl =>
      if (indom(x)(s)){
        if (app(s)(x) == t) matchs(tl,s) else throw new unifyException()
      } else {
        matchs(tl,(x,t) :: s)
      }
    case (t,V(x)) :: tl => throw new unifyException()
    case (T(f,ts),T(g,us)) :: tl =>
      if (f == g) matchs((ts zip us) ++ tl,s) else throw new unifyException()
  }

  def smatch(pat: Term,obj: Term): subst = matchs(List((pat,obj)),Nil)

  class normException extends Exception

  def rewrite(lt: List[(Term,Term)])(t: Term): Term = lt match{
    case Nil => throw new normException()
    case (l,r) :: rs =>
      try{ lift(smatch(l,t))(r) } catch{ case _: unifyException => rewrite(rs)(t) }
  }

  def norm(rs: List[(Term,Term)])(t: Term): Term = t match {
    case v@V(_) => v
    case T(f,ts) =>
      val u = T(f, ts map norm(rs))
      try{ norm(rs)(rewrite(rs)(u)) } catch { case _: normException => u }
  }
}
