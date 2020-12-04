theory tp89
imports Main "~~/src/HOL/Library/Code_Target_Nat" (* pour l'export Scala *)

begin

(* 
quickcheck_params [size=6,tester=narrowing,timeout=120]
nitpick_params [timeout=120]
*)

type_synonym transid= "nat*nat*nat"

datatype message= 
  Pay transid nat  
| Ack transid nat
| Cancel transid

datatype transBdd = list

type_synonym transaction= "transid * nat"

(* permet de mettre à jour une transBdd en fonction d'un nouveau message *)
fun traiterMessage:: "message \<Rightarrow> transBdd  \<Rightarrow> transBdd"
  where
"traiterMessage message transBdd = transBdd"

(* pour obtenir une liste de toutes les transactions validées d'une transBdd*)
fun export:: "transBdd \<Rightarrow> transaction list"
  where
"export transBdd = []"

(* permet d'obtenir une transBdd à partir d'une liste de messages *)
fun traiterMessageList:: "message list \<Rightarrow> transBdd"
  where
"(traiterMessageList (a#r)) = []"


(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end
