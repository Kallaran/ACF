package main

import library._
import org.junit.Assert._
import org.junit.Test
import simplifierProven.DERIEUX_Jean_DEMONGEOT_Nicolas.Simplify

class TestSimplify {
  @Test
  def t0(){
    val simp= new Simplify
    val p= List(Star)
    val pres= List(Star)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def t1(){
    val simp= new Simplify
    val p= List(Star,Star)
    val pres= List(Star)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def t2(){
    val simp= new Simplify

    val p= List(Star,Star, Char('a'), Char('a'),  Char('b'))
    val pres= List(Star,  Char('a'), Char('a'),  Char('b'))

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def t3(){
    val simp= new Simplify

    val p= List(Star,Star, Char('a'), Char('a'),  Char('b'), Star, Plus)
    val pres= List(Star,  Char('a'), Char('a'),  Char('b'), Plus)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def t4(){
    val simp= new Simplify

    val p= List(Star,Star, Char('a'), Char('a'),  Char('b'), Star, Plus, Qmark)
    val pres= List(Star,  Char('a'), Char('a'),  Char('b'), Plus, Qmark)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def t5(){
    val simp= new Simplify

    val p= List(Star,Star, Char('a'), Char('a'),  Char('b'), Star, Plus, Qmark, Plus)
    val pres= List(Star,  Char('a'), Char('a'),  Char('b'), Plus, Qmark, Plus)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def t6(){
    val simp= new Simplify

    val p= List(Star,Star, Char('a'), Char('a'),  Char('b'), Star, Plus, Qmark, Plus, Star, Star)
    val pres= List(Star,  Char('a'), Char('a'),  Char('b'), Plus, Qmark, Plus)

    assertEquals(pres, simp.simplify(p))
  }

  @Test
  def t7(){
    val simp= new Simplify

    val p= List(Qmark, Qmark, Star)
    val pres= List(Qmark, Plus)

    assertEquals(pres, simp.simplify(p))
  }
}