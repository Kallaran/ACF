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



(* Exercice 3 *)

lemma  "\<forall>(x::int) y  z. x + y > x + z \<longrightarrow> x + x > y + z"
  nitpick
  sorry
(*formule satisfaisable si 2x >y+z*)
lemma  "\<forall>(x::int) y  z.( x + y > x + z) \<and> (2 * x > y + z) \<longrightarrow> x + x > y + z"
  apply auto
  done

lemma "\<forall>(x::int) y. x + y \<le> x * y"
  nitpick
  sorry
(*formule satisfaisable si(x > 1) \<and> (y > 1)*)
lemma "\<forall>(x::int) y.  (x > 1) \<and> (y > 1) \<longrightarrow> (x + y \<le> x * y) "
  nitpick
  sorry

lemma "\<forall>(x::int)yz. x > y \<and> z > 0 \<longrightarrow> x * z > y * z" 
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

lemma appendCommu : "\<forall> a b. (length a#b)  = (length  b#a)  "
  oops


end