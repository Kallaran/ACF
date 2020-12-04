theory tp89
imports Main table "~~/src/HOL/Library/Code_Target_Nat" (* pour l'export Scala *)

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


type_synonym transaction= "transid * nat"

(* status correspond à (Valid, Amm, Amc, Canceled) *)
type_synonym status= "bool * nat * nat * bool" 
type_synonym transBdd = "(transid,  status) table"


(* permet de mettre à jour une transBdd en fonction d'un nouveau message *)
fun traiterMessage:: "message \<Rightarrow> transBdd  \<Rightarrow> transBdd"
  where
"traiterMessage message transBdd = transBdd"

(* pour obtenir une liste de toutes les transactions validées d'une transBdd*)
fun export:: "transBdd \<Rightarrow> transaction list"
  where
"export transBdd = []"

(* permet d'obtenir une transBdd à partir d'une liste de messages *)
fun traiterMessageList:: " message list  \<Rightarrow> transBdd"
  where
"(traiterMessageList [] ) = [] " |
"(traiterMessageList (x#rs)) = (traiterMessage x (traiterMessageList rs))"


(* Toutes les transactions validées ont un montant strictement supérieur à zero *)
lemma prop1:"(List.member (export (traiterMessageList a)) (transid, montant)) \<longrightarrow> (montant > 0) "
  nitpick[timeout=120]
  sorry

(* Toutes les transactions validées ont un montant strictement supérieur à zero *)
lemma prop1bis:"(List.member (export bdd) (transid, montant)) \<longrightarrow> (montant > 0) "
  nitpick[timeout=120]
  sorry


(* Dans la liste de transactions validées, tout triplet (c,m,i)  n'apparaît qu'une seule fois *)
lemma prop2:"\<not>(List.member (List.remove1 (transid, montanty) (export (traiterMessageList a)) ) (transid, montantx) )  "
  nitpick[timeout=120]
  sorry


(* Toute transaction (même validée) peut être annulée *)
(* interprétée ici comme : si un message 'cancel transid' est reçu alors le export de la bdd ne montrera pas de transaction ayant ce transid *)
lemma prop3:"\<not>(List.member ( export (traiterMessage (Cancel transid) (traiterMessageList a))) (transid, montant))"

(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end
