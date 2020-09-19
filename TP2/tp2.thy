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
value "isSet []" (* error, why ? *)
 

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

lemma " (member (a::int) (clean (b#c))) \<longrightarrow> ((a=b) = (\<not>(member a c))) \<or> ((a\<noteq>b) \<and> (member a c))  "
  nitpick
  sorry


(* Exercice 5 *)

lemma "(isSet (clean l))"
  sorry


end