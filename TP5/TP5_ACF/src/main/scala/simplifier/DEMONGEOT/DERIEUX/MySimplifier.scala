package simplifier.DEMONGEOT.DERIEUX

import library._

class MySimplifier extends Simplifier{

	def simplify(p: List[Symbol]): List[Symbol] = {
		p match {
			case Nil => Nil
			case Plus::Nil => List(Plus)
			case Star::Nil => List(Star)
			case Qmark::Nil=> List(Qmark)
			case Char(a)::Nil=> List(Char(a))

			case Char(a)::s=>Char(a)::simplify(s)
			case Star::Star::s => simplify(Star::s)
			case Plus::Plus::s => simplify(Qmark::Plus::s)
			case Qmark::Qmark::s => Qmark::simplify(Qmark::s)
			case Plus::Star::s => simplify(Plus::s)
			case Star::Plus::s => simplify(Plus::s)
			case Qmark::Plus::s => Qmark::simplify(Plus::s)
			case Plus::Qmark::s =>Plus::simplify(Qmark::s)

			case a::b::c => a::simplify(b::c)

		}

	}
		List()


}