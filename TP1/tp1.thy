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





end