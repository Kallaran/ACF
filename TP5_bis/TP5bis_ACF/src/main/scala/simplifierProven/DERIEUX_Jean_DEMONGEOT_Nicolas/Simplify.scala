package simplifierProven.DERIEUX_Jean_DEMONGEOT_Nicolas

import library._

class Simplify extends Simplifier{

	def simplify(x0: List[Symbol]): List[Symbol] = x0 match {
		case Nil => Nil
		case List(Plus) => List(Plus)
		case List(Star) => List(Star)
		case List(Qmark) => List(Qmark)
		case List(Char(a)) => List(Char(a))
		case Char(a) :: v :: va => Char(a) :: simplify(v :: va)
		case Star :: Star :: s => simplify(Star :: s)
		case Plus :: Plus :: s => Plus :: simplify(Plus :: s)
		case Qmark :: Qmark :: s => Qmark :: simplify(Qmark :: s)
		case Plus :: Star :: s => simplify(Plus :: s)
		case Star :: Plus :: s => simplify(Plus :: s)
		case Qmark :: Plus :: s => Qmark :: simplify(Plus :: s)
		case Plus :: Qmark :: s => Plus :: simplify(Qmark :: s)
		case Qmark :: Star :: s => simplify(Plus :: s)
		case Star :: Qmark :: s => simplify(Plus :: s)
		case Star :: Char(v) :: c => Star :: simplify(Char(v) :: c)
		case Qmark :: Char(v) :: c => Qmark :: simplify(Char(v) :: c)
		case Plus :: Char(v) :: c => Plus :: simplify(Char(v) :: c)
	}
}