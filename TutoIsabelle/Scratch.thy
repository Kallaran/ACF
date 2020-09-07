theory Scratch
  imports Main
begin

  fun remove:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "remove x [] = []" |
    "remove x (z#ys) = (if x=z then (remove x ys) else z#(remove x ys))"
  
  value "remove (2::int) [1,2,3]" (* this is a simple test *)
  value "remove (1::int) [1,1]"


lemma " \<not>(List.member (remove e l) e)"
  apply(induct l)
  apply auto
  apply (simp add: member_rec(2))
  by (simp add: member_rec(1))
    
lemma count_remove : "(length l) = (length (remove e l)) + (count_list l e)"
  apply(induct l)
  apply auto
  done

lemma "(length (remove e l)) = (length l) \<longrightarrow>   \<not>(List.member l e)"
  apply (induct l)
  apply auto
  apply (simp add: member_rec(2))
  apply (metis Suc_n_not_le_n count_remove le_add_same_cancel1 zero_le)
  apply (metis add.right_neutral add_Suc_right add_left_cancel count_remove nat.simps(3))
  by (simp add: member_rec(1))




    
datatype 'a tree= Leaf | Node 'a "'a tree" "'a tree"
definition "myTree= Node (1::int) (Node 2 Leaf Leaf) (Node 3 Leaf Leaf)"


fun numNodes:: "'a tree \<Rightarrow> nat"
where
"numNodes Leaf = 0" |
"numNodes (Node e t1 t2) = 1+(numNodes t1)+(numNodes t2)"


fun subTree:: "'a tree \<Rightarrow> 'a tree \<Rightarrow> bool"
where
"subTree Leaf Leaf = True" |
"subTree t Leaf = False" |
"subTree t (Node e t1 t2) = ((t=(Node e t1 t2)) \<or> (subTree t t1) \<or> (subTree t t2))"


value "numNodes myTree"
value "subTree (Node 3 Leaf Leaf) myTree"

lemma subNum: "(subTree t1 t2) \<longrightarrow> (numNodes t1) \<le> (numNodes t2)"
  apply auto
  apply (induct t2)
  using subTree.elims(2) apply blast
  apply auto
  done


export_code remove numNodes subTree in Scala


end