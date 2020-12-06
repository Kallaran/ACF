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

datatype typeAbs = Define nat | Undefine


(* status correspond à (Valid, Amm, Amc, Canceled) *)
type_synonym status= "bool * typeAbs * nat * bool" 
type_synonym transBdd = "(transid,  status) table"



(* permet de savoir si une transid  est deja presente dans une Bdd *)
fun isTransidPresent:: "'b option \<Rightarrow> bool"
  where
"(isTransidPresent None)  = False  " |
"(isTransidPresent (Some(y)) ) = True "

(* rend le boolean True si le typeAbs est Define *)
fun isDefine:: "typeAbs \<Rightarrow> bool"
  where
"isDefine Undefine = False" |
"isDefine _ = True"

(* permet d'obtenir le nat d'un Define nat d'un typeAbs *)
fun getNat:: "typeAbs \<Rightarrow> nat"
  where
"getNat Undefine = 0" | (*ce cas n'est pas censé arriver *)
"getNat (Define x) = x"


(* permet d'obtenir le nouveau quadruplet lors d'un message Pay *)
fun updatePay:: "nat \<Rightarrow> (bool * typeAbs * nat * bool) option \<Rightarrow> (bool * typeAbs * nat * bool)"
  where
"updatePay Amc None = (False, Undefine, 0, True)" | (* ce cas n'est pas censé arriver *)
"updatePay Amc (Some(Valid,  Amm , oldAmc , Canceled)) = (if (Valid \<or> Canceled) 
                                                          then (Valid , Amm , oldAmc , Canceled) 
                                                          else (if ((Amc \<ge> (getNat Amm)) \<and> (Amc > 0)) 
                                                                then (True, Amm, Amc, Canceled) 
                                                                else (if (Amc > oldAmc)
                                                                      then (Valid, Amm, Amc, Canceled)
                                                                      else (Valid, Amm, oldAmc, Canceled)))) "

(* permet d'obtenir le nouveau quadruplet lors d'un message Ack *)
fun updateAck:: "nat \<Rightarrow> (bool * typeAbs * nat * bool) option \<Rightarrow> (bool * typeAbs * nat * bool)"
  where
"updateAck Amm None = (False, Undefine, 0, True)" | (* ce cas n'est pas censé arriver *)
"updateAck Amm (Some(Valid,  oldAmm , Amc , Canceled)) = (if (Valid \<or> Canceled) 
                                                          then (Valid , oldAmm , Amc , Canceled) 
                                                          else (if ((Amm \<le> Amc) \<and> (Amc > 0)) 
                                                                then (True, (Define Amm), Amc, Canceled) 
                                                                else (if (\<not>(isDefine oldAmm) \<or>  (Amm < (getNat oldAmm)))
                                                                      then (Valid,(Define Amm), Amc, Canceled)
                                                                      else (Valid, oldAmm, Amc, Canceled)))) "


(* permet de mettre à jour une transBdd en fonction d'un nouveau message *)
fun traiterMessage:: "message \<Rightarrow> transBdd  \<Rightarrow> transBdd"
  where
"traiterMessage (Cancel transid)  transBdd = (modify transid (False, Undefine, 0, True) transBdd)" |
"traiterMessage (Pay transid Amc)  transBdd = (if (isTransidPresent (assoc transid transBdd)) then (modify transid (updatePay Amc (assoc transid transBdd)) transBdd ) else (modify transid (False, Undefine, Amc, False) transBdd) )" |
"traiterMessage (Ack transid Amm)  transBdd = (if (isTransidPresent (assoc transid transBdd)) then (modify transid (updateAck Amm (assoc transid transBdd)) transBdd ) else (modify transid (False, (Define Amm), 0, False) transBdd) )"



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
(*  rajouter des messages ne change pas l'annulation, on en rajoute 2 messagey et messagex car c'est le nombre de message minimum qu'il faut pour valider une transaction *)
lemma prop4:"\<not>(List.member ( export (traiterMessage messagey (traiterMessage messagex (traiterMessage (Cancel transid) (traiterMessageList a))))) (transid, montant))"
  nitpick[timeout=120]
  sorry

(* Si un message Pay et un message Ack avec un même identifiant (c, m, i) ont éte envoyés, tels que
 le montant proposé par le Pay est strictement supérieur à 0, et est supérieur ou égal au montant
proposé par le message Ack, et s'il n'y a pas eu d'annulation pour (c, m, i), alors une transaction
pour (c, m, i) figure dans la liste des transactions validées *)
(* j'utilise une transBdd [] car je ne vois pas comment garantir sans cela qu'il n'y a pas eu d'annulation *)
(* je pourrai vérifier que le transid ne se trouve pas dans la Bdd mais ça ne serait pas totalement exact aussi *)
(* je pourrai créer une fonction qui prend un transid et une Bdd et qui rend le bool correspondant à Canceled mais ça serait contraire à l'énoncé *)
lemma prop5:"(List.member ( export (traiterMessage  (Ack transid  Amm) (traiterMessage (Pay transid Amc) []))) (transid, Amc)) = ((Amc > 0) \<and> (Amc \<ge> Amm))  "
  nitpick[timeout=120]
  sorry

(* Toute transaction figurant dans la liste des transactions validées l'a été par un message Pay et un
message Ack tels que le montant proposé par le Pay est supérieur ou égal au montant proposé par le
message Ack *)
(* vu ici comme si une transaction n'est pas dans la liste des transaction validée et qu'on a la même Bdd mais à qui on rajoute les messages  Pay transid Amc et Ack transid Amm et que la transaction est bien présent dans l'export alors ça implique que  Amc \<ge> Amm et Amc > 0 *)

lemma prop6: "(\<not>(List.member (export (traiterMessageList a)) (transid, montant)) \<and> (List.member (export (traiterMessage (Ack transid Amm ) (traiterMessage (Pay transid Amc)  (traiterMessageList a)))) (transid, montant))) \<longrightarrow> (Amc\<ge>Amm)    "
  nitpick[timeout=120]
  oups

(* comme prop6 mais permet de vérifier que Amc > 0 *)
(* j'utilise List.count_list pour assurer qu'il n'existe pas dans la transBdd une transaction transid avec un Amc = 0 *)
lemma prop6bis: "(((List.count_list (traiterMessageList a) (transid, (Valid, oldAmm, 0, Canceled))) = 0 ) \<and>(\<not>(List.member (export (traiterMessageList a)) (transid, montant)) \<and> (List.member (export (traiterMessage (Ack transid Amm ) (traiterMessage (Pay transid Amc)  (traiterMessageList a)))) (transid, montant)))) \<longrightarrow> ((Amc\<ge>Amm) \<and> (Amc > 0))    "
  nitpick[timeout=120]
  oups


(*Si un client (resp. marchand) a proposé un montant am pour une transaction, tout montant am'
inférieur (resp. supérieur) proposé par la suite est ignoré par l'agent de validation *)
lemma prop7: "True"
  nitpick[timeout=120]
  sorry

(* ----- Exportation en Scala (Isabelle 2018) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end
