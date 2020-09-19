theory tp1
imports Main
begin

lemma "A \<or> B"
  nitpick
  oops

lemma "A \<and> B \<longrightarrow> B"
  apply auto
  done


(* Exercice 1 *)

lemma "A \<and> (B \<or> C) \<longleftrightarrow> (A \<and> B) \<or> (A \<and> C)"
  apply auto
  done

lemma "\<not>(A \<and> B) \<longleftrightarrow> \<not>A \<or> \<not>B"
  apply auto
  done


(* Exercice 2 *)

lemma "(R \<longrightarrow> K) 
\<and> (M \<longrightarrow> \<not>D ) 
\<and> (D \<longleftrightarrow> E)  
\<and> (K \<longrightarrow> (E \<and> M))  
\<and> (E \<longrightarrow> K)"
  nitpick
  oops



(* Exercice 3 *)

lemma  "\<forall>(x::nat) y  z. x + y > x + z \<longrightarrow> x + x > y + z"
  nitpick
  sorry
(*formule satisfaisable si 2x >y+z*)
lemma  "\<forall>(x::nat) y  z.( x + y > x + z) \<and> (2 * x > y + z) \<longrightarrow> x + x > y + z"
  apply auto
  done

lemma "\<forall>(x::nat) y. x + y \<le> x * y"
  nitpick
  sorry
(*formule satisfaisable si (x > 1) \<and> (y > 1) *)
lemma "\<forall>(x::nat) y.  (x > 1) \<and> (y > 1) \<longrightarrow> (x + y \<le> x * y) "
  apply auto
  sorry

lemma "\<forall>(x::nat)yz. x > y \<and> z > 0 \<longrightarrow> x * z > y * z" 
  apply auto
  done (*formule valide*)

lemma "\<exists>x. P(f(x)) \<longrightarrow> (\<forall>x. P(f(x)))"
  apply auto
  done(*formule valide*)



(* Exercice 4 *)

lemma commu :"\<forall> (A::int)B. (A + B) = (B + A) "
  apply auto
  done

lemma asso : "\<forall> (A::int) B C. (A + B) + C = A + (B + C)"
  apply auto
  done

lemma neutre : "\<exists>  (A::int). A + B = B"
  apply auto
  done

(* Exercice 5 *)

lemma appendCommu : "( append a b )  = ( append b a ) "
  oops


lemma appendAsso :"( append ( append a b ) c )  = ( append a ( append b c ) ) "
  apply auto
  done

lemma appendNeutre : "\<exists>x. (append x  b) = b  "
  apply auto
  done

(* Exercice 6 *)


lemma "(length (append a b)) = (length  a) + (length b)" 
  apply auto
  done


fun suc::"nat \<Rightarrow> nat"
  where
"suc x = x+1"

lemma "  (map suc  (append a b))  = (append (map suc a) (map suc b))   "
  apply auto
  done

lemma " (List.member l a) \<longrightarrow>  (List.member (append l m ) a)  "
  apply auto
  by (metis UnCI in_set_member set_append)




end