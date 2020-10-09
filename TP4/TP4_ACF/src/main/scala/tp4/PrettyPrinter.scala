package tp4

object PrettyPrinter {

  def stringOf(e:Expression):String={
    e match{
      case IntegerValue(i) => i.toString
      case VariableRef(v) => v
      case BinExpression(op, e1, e2) => "( " + stringOf(e1) + stringOf(op) + stringOf(e2) + " )"
    }
  }

  def stringOf(e:Operator):String= {
    e match {
      case Plus => " + "
      case Minus => " - "
      case Times => " * "
      case Inf => " < "
      case Infeq => " <= "
      case Equal => " = "
    }
  }

  def stringOf(e:Statement):String= {
    e match {
      case Seq(s1:Statement,s2:Statement) => stringOf(s1) + stringOf(s2)
      case If(c:Expression,s1:Statement,s2:Statement) => "if (" + stringOf(c) + ")" + "{\n" + stringOf(s1) + stringOf(s2) + "}\n"
      case While(c:Expression,s:Statement) => "while (" + stringOf(c) + ")" + " do\n" + "{\n" + stringOf(s) + "}\n"
      case Assignement(v:String,e:Expression) => v + ":= "+ stringOf(e) + "\n"
      case Print(e:Expression) => "print(" + stringOf(e) + ")\n"
      case Read(s:String) => "read("+ s + ")\n"
    }
  }




}
