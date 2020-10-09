theory tp2
imports Main
begin



(* Exercice 1 *)

fun member:: " 'a \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"(member b Nil) = False" |
"(member b (Cons c d)) = (if b=c then True else (member b d))" 

value "member (1::int) [1, 2, 3]"
value "member (1::int) [2, 4]"
value "member (1::int) []"


(* Exercice 2 *)


fun isSet:: "'a list \<Rightarrow> bool"
  where
"(isSet [])  = True"|
"(isSet (a#b)) = (if (member a b) then False else (isSet b))"

value "isSet [(1::int), 2, 3]"
value "isSet [(1::int), 1, 3]"
value "isSet ([]::int list)" 
 

(* Exercice 3 *)

fun clean:: "'a list \<Rightarrow> 'a list"
  where
"clean [] = []"|
"clean (a#b) = (if (member a b) then (clean b) else (a#(clean b)))"

value "clean [(1::int),2,3]"
value "clean [(1::int),1,3]"
value "clean [(1::int),1,2,2,2,4]"
value "clean [(1::int)]"


(* Exercice 4 *)

lemma lem4: "  (member a l) = (member a (clean l)) "
  apply auto
  apply (induct l)
  apply auto
  apply (induct l)
  apply auto
  by (metis (full_types) tp2.member.simps(2))


(* Exercice 5 *)

lemma lem5: "(isSet (clean l))"
  apply (induct l)
   apply auto
  by (meson lem4)

(* Exercice 6 *)

fun delete:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"(delete x []) = []"|
"(delete a (b#c)) = (if (a=b)then (delete a c) else b#(delete a c))  "

value "delete 2 [(1::int),2,3]"
value "delete 2 [(1::int),1,3]"
value "delete 2 [(1::int),1,2,2,2,4]"
value "delete 2 [(1::int)]"

(* Exercice 7 *)

(* un élément supprimé avec delete dans un ensemble ne doit plus appartenir à cet ensemble *)
lemma lem71: "\<not>(member a (delete a l))"
  apply (induct l)
  apply auto
  done

(* si un élément est présent dans l'ensemble et qu'il n'est pas l'élément à supprimer, *)
(* alors il doit rester présent dans cet ensemble *)
lemma lem72: "((member a l) \<and> ( a \<noteq> b) ) \<longrightarrow>  ( member a (delete b l))"
  apply auto
  apply (induct l)
  apply auto
  done

lemma lem72prof: "(isSet l) \<longrightarrow> (x\<noteq>y) \<longrightarrow>(member y (delete x l)  \<longleftrightarrow>(member y l))"
  apply auto
   apply (induct l)
    apply auto
   apply (metis (full_types) tp2.member.simps(2))
  by (simp add: lem72)

(* Exercice 8 *)

fun intersection:: " 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"(intersection [] []) = []" |
"(intersection [] _ ) = []" |
"(intersection (a#b) c) = (if (member a c) then (a#(intersection b c)) else (intersection b c))"


value "(intersection [(1::int), 2, 3] [3, 4])"
value "(intersection [(1::int), 2, 3] [1, 3, 3])"


(* Exercice 9 *)

(* si un élément est membre à la fois dans les 2 listes alors il est présent dans l'intersection des 2 *)
lemma lem9:  "((member a l) \<and> (member a m)) \<longrightarrow> (member a (intersection l m))"
  apply auto
  apply (induct l)
  apply auto
  done

lemma lem9prof: "(isSet l1) \<longrightarrow> (isSet l2) \<longrightarrow> (member x (intersection l1 l2)) =  ((member x l1) \<and> (member x l2))"
    apply (induct l1)
  apply auto
     apply (induct l2)
   apply auto
  done


(* Exercice 10 *)

(* vérifions que le résultat de 'intersection' satisfait le 'isSet' *)
lemma lem10:  "(isSet l) \<and> (isSet m) \<longrightarrow> ( isSet (intersection l m))"
  apply (induct l)
   apply auto
     apply (induct m)
  apply auto
  by (simp add: lem9prof)


(* Exercice 11 *)

fun union:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"(union [] []) = []" |
"(union [] a ) = (clean a)" |
"(union (a#b) l) = (clean (a#(union b l))) "

value "(union [(1::int), 2, 3] [4,5,6])"
value "(union [(1::int), 2, 3, 4] [4,5,6,6])"
value "(union [] [(0::int),0])"


(* Exercice 12 *)

(* si un élément est présent dans un emsemble alors il est présent dans le résultat *)
lemma lem12: "(member a l) \<longrightarrow> (member a (union b l))"
  apply (induct l)
    apply (induct b)
    apply auto
  sorry


lemma lem12prof: "(isSet l1) \<longrightarrow> (isSet l2) \<longrightarrow> ((member x (union l1 l2)) =  (member x l1) \<or> (member x l2))"
  apply (induct l1)
  apply (induct l2)
    apply auto
  apply (meson lem4)
  apply (meson lem4)
  apply (meson lem4)
  apply (meson lem4)
  by (meson lem4)


(* Exercice 13 *)

lemma lem13: " (isSet (union l  m))"
  apply (induct l)
   apply auto
  apply (metis isSet.cases isSet.elims(3) lem5 union.simps(1) union.simps(2))
    apply (simp add: lem5)
  apply (meson lem4)
  by (simp add: lem5)


lemma lem13prof: "(isSet l1) \<longrightarrow> (isSet l2) \<longrightarrow> (isSet (union l1 l2))"
  apply (induct l1)
   apply (induct l2)
  apply simp
  using lem13 apply blast
  using lem13 by blast


(* Exercice 14 *)

fun equal::"'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"(equal [] []) = True"|
"(equal [] _ ) = False" |
"(equal _ []) = False" |
"(equal (a#b) (c#d)) = (if (a=c) then (equal b d) else False)"


(* Exercice 15 *)

(* si l et m sont égaux et que a est dans l alors a est également dans m *)
lemma lem15: "(equal l m) \<and> (member a l) \<longrightarrow> ( member a m)"
  nitpick
  apply auto
  apply (induct l)
   apply auto
  sorry


lemma lem1prof: "(isSet l1) \<longrightarrow> (isSet l2) \<longrightarrow> ((equal l1 l2) = ( \<forall>x. ((member x l1) = (member x l1))))"
  sorry






end