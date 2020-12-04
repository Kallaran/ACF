package validator.DERIEUX_DEMONGEOT

import bank._


// Automatic conversion of bank.message to tp89.messages and Nat to bank.Nat
object Converter{
  implicit def bank2message(m:bank.message):tp89.message=
    m match {
    case bank.Pay((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p)) => tp89.Pay((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))
    case bank.Ack((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p)) => tp89.Ack((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))
    case bank.Cancel((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i)))) => tp89.Cancel((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))))
  }
  
  implicit def trans2bankTrans(l:List[((Nat.nat,(Nat.nat,Nat.nat)),Nat.nat)]): List[((bank.Nat.nat,(bank.Nat.nat,bank.Nat.nat)),bank.Nat.nat)]=
    l match {
    case Nil => Nil
    case ((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))::r => ((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p))::trans2bankTrans(r)
  }
}

import Converter._


class ConcreteValidator extends TransValidator{

  var transBdd:List[((Nat.nat, (Nat.nat, Nat.nat)), (Boolean, (tp89.typeAbs, (Nat.nat, Boolean))))] = List()
  def process(m:message):Unit={
    transBdd = tp89.traiterMessage(m, transBdd )
  }

  def getValidTrans={
    tp89.`export`(transBdd)
  }
}


object HOL {

  trait equal[A] {
    val `HOL.equal`: (A, A) => Boolean
  }
  def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
  object equal {
    implicit def `Product_Type.equal_prod`[A : equal, B : equal]: equal[(A, B)] =
      new equal[(A, B)] {
        val `HOL.equal` = (a: (A, B), b: (A, B)) =>
          Product_Type.equal_proda[A, B](a, b)
      }
    implicit def `Nat.equal_nat`: equal[Nat.nat] = new equal[Nat.nat] {
      val `HOL.equal` = (a: Nat.nat, b: Nat.nat) => Nat.equal_nata(a, b)
    }
  }

  def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Code_Numeral {

  def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
    case Nat.Nata(x) => x
  }

} /* object Code_Numeral */



object Product_Type {

  def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
    (x0, x1) match {
      case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
    }

} /* object Product_Type */

object table {

  abstract sealed class option[A]
  final case class Somea[A](a: A) extends option[A]
  final case class Nonea[A]() extends option[A]

  def assoc[A : HOL.equal, B](uu: A, x1: List[(A, B)]): option[B] = (uu, x1) match
  {
    case (uu, Nil) => Nonea[B]()
    case (x1, (x, y) :: xs) =>
      (if (HOL.eq[A](x, x1)) Somea[B](y) else assoc[A, B](x1, xs))
  }

  def modify[A : HOL.equal, B](x: A, y: B, xa2: List[(A, B)]): List[(A, B)] =
    (x, y, xa2) match {
      case (x, y, Nil) => List((x, y))
      case (x, y, (z, u) :: r) =>
        (if (HOL.eq[A](x, z)) (x, y) :: r else (z, u) :: modify[A, B](x, y, r))
    }

} /* object table */

object tp89 {

  abstract sealed class message
  final case class Pay(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends
    message
  final case class Ack(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends
    message
  final case class Cancel(a: (Nat.nat, (Nat.nat, Nat.nat))) extends message

  abstract sealed class typeAbs
  final case class Define(a: Nat.nat) extends typeAbs
  final case class Undefine() extends typeAbs

  def export(x0: List[((Nat.nat, (Nat.nat, Nat.nat)),
    (Boolean, (typeAbs, (Nat.nat, Boolean))))]):
  List[((Nat.nat, (Nat.nat, Nat.nat)), Nat.nat)]
  =
    x0 match {
      case Nil => Nil
      case (transid, (true, (amm, (amc, false)))) :: rs =>
        (transid, amc) :: export(rs)
      case (transid, (false, (uv, (uw, ux)))) :: rs => export(rs)
      case (transid, (uu, (uv, (uw, true)))) :: rs => export(rs)
    }

  def getNat(x0: typeAbs): Nat.nat = x0 match {
    case Undefine() => Nat.zero_nat
    case Define(x) => x
  }

  def isDefine(x0: typeAbs): Boolean = x0 match {
    case Undefine() => false
    case Define(v) => true
  }

  def updateAck(amm: Nat.nat,
                x1: table.option[(Boolean, (typeAbs, (Nat.nat, Boolean)))]):
  (Boolean, (typeAbs, (Nat.nat, Boolean)))
  =
    (amm, x1) match {
      case (amm, table.Nonea()) => (false, (Undefine(), (Nat.zero_nat, true)))
      case (amm, table.Somea((valid, (oldAmm, (amc, canceled))))) =>
        (if (valid || canceled) (valid, (oldAmm, (amc, canceled)))
        else (if (Nat.less_eq_nat(amm, amc) && Nat.less_nat(Nat.zero_nat, amc))
          (true, (Define(amm), (amc, canceled)))
        else (if (! (isDefine(oldAmm)) ||
          Nat.less_nat(amm, getNat(oldAmm)))
          (valid, (Define(amm), (amc, canceled)))
        else (valid, (oldAmm, (amc, canceled))))))
    }

  def updatePay(amc: Nat.nat,
                x1: table.option[(Boolean, (typeAbs, (Nat.nat, Boolean)))]):
  (Boolean, (typeAbs, (Nat.nat, Boolean)))
  =
    (amc, x1) match {
      case (amc, table.Nonea()) => (false, (Undefine(), (Nat.zero_nat, true)))
      case (amc, table.Somea((valid, (amm, (oldAmc, canceled))))) =>
        (if (valid || canceled) (valid, (amm, (oldAmc, canceled)))
        else (if (Nat.less_eq_nat(getNat(amm), amc) &&
          Nat.less_nat(Nat.zero_nat, amc))
          (true, (amm, (amc, canceled)))
        else (if (Nat.less_nat(oldAmc, amc))
          (valid, (amm, (amc, canceled)))
        else (valid, (amm, (oldAmc, canceled))))))
    }

  def isTransidPresent[A](x0: table.option[A]): Boolean = x0 match {
    case table.Nonea() => false
    case table.Somea(y) => true
  }

  def traiterMessage(x0: message,
                     transBdd:
                     List[((Nat.nat, (Nat.nat, Nat.nat)),
                       (Boolean, (typeAbs, (Nat.nat, Boolean))))]):
  List[((Nat.nat, (Nat.nat, Nat.nat)),
    (Boolean, (typeAbs, (Nat.nat, Boolean))))]
  =
    (x0, transBdd) match {
      case (Cancel(transid), transBdd) =>
        table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
          (Boolean,
            (typeAbs,
              (Nat.nat,
                Boolean)))](transid,
          (false,
            (Undefine(), (Nat.zero_nat, true))),
          transBdd)
      case (Pay(transid, amc), transBdd) =>
        (if (isTransidPresent[(Boolean,
          (typeAbs,
            (Nat.nat,
              Boolean)))](table.assoc[(Nat.nat,
          (Nat.nat, Nat.nat)),
          (Boolean, (typeAbs, (Nat.nat, Boolean)))](transid, transBdd)))
          table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
            (Boolean,
              (typeAbs,
                (Nat.nat,
                  Boolean)))](transid,
            updatePay(amc,
              table.assoc[(Nat.nat, (Nat.nat, Nat.nat)),
                (Boolean,
                  (typeAbs, (Nat.nat, Boolean)))](transid, transBdd)),
            transBdd)
        else table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
          (Boolean,
            (typeAbs,
              (Nat.nat,
                Boolean)))](transid,
          (false, (Undefine(), (amc, false))), transBdd))
      case (Ack(transid, amm), transBdd) =>
        (if (isTransidPresent[(Boolean,
          (typeAbs,
            (Nat.nat,
              Boolean)))](table.assoc[(Nat.nat,
          (Nat.nat, Nat.nat)),
          (Boolean, (typeAbs, (Nat.nat, Boolean)))](transid, transBdd)))
          table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
            (Boolean,
              (typeAbs,
                (Nat.nat,
                  Boolean)))](transid,
            updateAck(amm,
              table.assoc[(Nat.nat, (Nat.nat, Nat.nat)),
                (Boolean,
                  (typeAbs, (Nat.nat, Boolean)))](transid, transBdd)),
            transBdd)
        else table.modify[(Nat.nat, (Nat.nat, Nat.nat)),
          (Boolean,
            (typeAbs,
              (Nat.nat,
                Boolean)))](transid,
          (false, (Define(amm), (Nat.zero_nat, false))), transBdd))
    }

} /* object tp89 */
