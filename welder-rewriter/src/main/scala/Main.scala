// Following book Term rewriting and all that
object Main{
  import TRS._

  def main(args: Array[String]): Unit = {
    val e = T("e",List())
    val x = V("x",1)
    val rule1 = (T("*",List(e,x)),x)
    print(norm(List(rule1))(T("*",List(e,x))))  }

}