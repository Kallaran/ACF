package tp4

object Interpret {
  def eval(p:Statement, inList:List[Int]):List[Int]= {

    p match {
      case Seq(s1:Statement,s2:Statement) => stringOf(s1) + stringOf(s2)
      case If(c:Expression,s1:Statement,s2:Statement) => "if (" + stringOf(c) + ")" + "{\n" + stringOf(s1) + stringOf(s2) + "}\n"
      case While(c:Expression,s:Statement) => "while (" + stringOf(c) + ")" + " do\n" + "{\n" + stringOf(s) + "}\n"
      case Assignement(v:String,e:Expression) => v + ":= "+ stringOf(e) + "\n"
      case Print(e:Expression) => "print(" + stringOf(e) + ")\n"
      case Read(s:String) =>
    }
  }
    def eval(e:Expression):Int ={
      e match{
        case IntegerValue(i) => i
        case VariableRef(v) =>
        case BinExpression(op, e1, e2) => operationInt(op, e1, e2)
      }
    }




  def operationInt(e:Operator, e1:Expression, e2:Expression):Int= {
    e match {
      case Plus => eval(e1) + eval(e2)
      case Minus => eval(e1) - eval(e2)
      case Times => eval(e1) * eval(e2)
      case Inf => if (eval(e1) < eval(e2)) {1} else {0}
      case Infeq => if (eval(e1) <= eval(e2)) {1} else {0}
      case Equal => if (eval(e1) == eval(e2)) {1} else {0}
    }
  }





}
