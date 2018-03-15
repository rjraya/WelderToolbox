// Following book Term rewriting and all that

import TRS._

object Orders{

  object Order extends Enumeration{
    type Order = Value
    val GR, EQ, NGE = Value
  }

  import Order._

  // Order for function symbols
  def ordFs(s: String, t: String): Order = {
    /*
          TODO: this should implement a list of pairs (f,g) meaning f > g
          and applies transitive closure of this list meaning that if
          (f,g),(g,h) then (f,h)
     */

    EQ
  }

  def lex(ord)(x:List[],y: List[]) = (x,y) match{
    case (Nil,Nil) => EQ
    case (x::xs,y::ys) => ord(x,y) match{
      case GR => GR
      case EQ => lex(ord)(xs,ys)
      case NGE => NGE
    }
  }


  def lpo(ord: (String,String) => Order)(s: Term,t: Term): Order = (s,t) match{
    case (_,V(x)) =>
      if(s == t) EQ
      else if(occurs(x)(s)) GR else NGE
    case (V(_),V(_)) => NGE
    case (T(f,ss),T(g,ts)) =>
      if(ss forall{si => lpo(ord)(si,t) == NGE}) ord(f,g) match{
        case GR =>
          if(ts forall{ti => lpo(ord)(s,ti) == GR}) GR
          else NGE
        case EQ =>
          if(ts forall{ti => lpo(ord)(s,ti) == GR}) lex (lpo(ord))(ss,ts)
          else NGE
        case NGE => NGE
      }
      else {
        Order.GR
      }
  }

  def rpo(stat)(ord)(s: List[Term],t:List[Term]): Order = (s,t) match{
    case (s,V(x)) =>
      if(s == t) EQ
      else if(occurs(x)(s)) GR else NGE
    case (V(_),T(_)) => NGE
    case (T(f,ss),T(g,ts)) =>
      if(ss forall{si => rpo(stat)(ord)(si,t) == NGE}) ord(f,g) match{
        case GR =>
          if(ts forall{ti => rpo(stat)(ord)(s,ti) == GR}) GR
          else NGE
        case EQ =>
          if(ts forall{ti => rpo(stat)(ord)(s,ti) == GR}) (stat(f))(rpo(stat)(ord))(ss,ts)
          else NGE
        case NGE => NGE
      }
      else{
        GR
      }
  }

}





