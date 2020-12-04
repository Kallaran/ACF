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



(* permet de savoir si une transid  est deja presente dans une Bdd *)
fun isTransidPresent:: "'b option \<Rightarrow> bool"
  where
"(isTransidPresent None)  = False  " |
"(isTransidPresent (Some(y)) ) = True "

(* permet d'obtenir le nouveau quadruplet lors d'un message Pay *)
fun updatePay:: "nat \<Rightarrow> (bool * nat * nat * bool) option \<Rightarrow> (bool * nat * nat * bool)"
  where
"updatePay Amc None = (False, 0, 0, True)" | (* ce cas n'est pas censé arriver *)
"updatePay Amc (Some(Valid,  Amm , oldAmc , Canceled)) = (if (Valid \<or> Canceled) 
                                                          then (Valid , Amm , oldAmc , Canceled) 
                                                          else (if ((Amc \<ge> Amm) \<and> (Amc > 0)) 
                                                                then (True, Amm, Amc, Canceled) 
                                                                else (if (Amc > oldAmc)
                                                                      then (Valid, Amm, Amc, Canceled)
                                                                      else (Valid, Amm, oldAmc, Canceled)))) "

(* permet d'obtenir le nouveau quadruplet lors d'un message Ack *)
fun updateAck:: "nat \<Rightarrow> (bool * nat * nat * bool) option \<Rightarrow> (bool * nat * nat * bool)"
  where
"updateAck Amm None = (False, 0, 0, True)" | (* ce cas n'est pas censé arriver *)
"updateAck Amm (Some(Valid,  oldAmm , Amc , Canceled)) = (if (Valid \<or> Canceled) 
                                                          then (Valid , oldAmm , Amc , Canceled) 
                                                          else (if ((Amm \<le> Amc) \<and> (Amc > 0)) 
                                                                then (True, Amm, Amc, Canceled) 
                                                                else (if (Amm < oldAmm)
                                                                      then (Valid, Amm, Amc, Canceled)
                                                                      else (Valid, oldAmm, Amc, Canceled)))) "


(* permet de mettre à jour une transBdd en fonction d'un nouveau message *)
fun traiterMessage:: "message \<Rightarrow> transBdd  \<Rightarrow> transBdd"
  where
"traiterMessage (Cancel transid)  transBdd = (modify transid (False, 0, 0, True) transBdd)" | (* EST CE INTERESSANT DE CONSERVER LES ANCIENNES VALEURS ? *)
"traiterMessage (Pay transid Amc)  transBdd = (if (isTransidPresent (assoc transid transBdd)) then (modify transid (updatePay Amc (assoc transid transBdd)) transBdd ) else (modify transid (False, 0, Amc, False) transBdd) )" | (* AI JE RAISON DE METTRE AMM A 0 LORS DE LA CREATION  ? *)
"traiterMessage (Ack transid Amm)  transBdd = (if (isTransidPresent (assoc transid transBdd)) then (modify transid (updateAck Amm (assoc transid transBdd)) transBdd ) else (modify transid (False, Amm, 0, False) transBdd) )"



(* pour obtenir une liste de toutes les transactions validées d'une transBdd*)
fun export:: "transBdd \<Rightarrow> transaction list"
  where
"export [] = []" |
"export ((transid, (True, Amm, Amc, False))#rs) = (transid, Amc)#(export rs)" | (*cas transaction valide et non canceled *)
"export ((transid, (_, _, _, _))#rs) = (export rs)"

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
  nitpick[timeout=120]
  sorry

(* Toute transaction annulée l'est définitivement : un message (Cancel (c,m,i)) rend impossible la validation d'une transaction de numéro i entre un marchand m et un client c *)
(* ASK : EN QUOI EST CE DIFFERENT DE PROP3 ? *)
lemma prop4:"True"
  nitpick[timeout=120]
  sorry

(* Si un message Pay et un message Ack avec un même identifiant (c, m, i) ont éte envoyés, tels que
 le montant proposé par le Pay est strictement supérieur à 0, et est supérieur ou égal au montant
proposé par le message Ack, et s'il n'y a pas eu d'annulation pour (c, m, i), alors une transaction
pour (c, m, i) figure dans la liste des transactions validées *)
(* ASK : COMMENT ON FAIT POUR SAVOIR SI IL N'Y A PAS EU D'ANNULATION ? *)
lemma prop5:"True"
  nitpick[timeout=120]
  sorry



(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end
