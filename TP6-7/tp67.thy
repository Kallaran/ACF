theory tp67
imports Main  "~~/src/HOL/Library/Code_Target_Int" 
begin

(* Types des expressions, conditions et programmes (statement) *)
datatype expression= Constant int | Variable string | Sum expression expression | Sub expression expression

datatype condition= Eq expression expression

datatype statement= Seq statement statement | 
                    Aff string expression | 
                    Read string | 
                    Print expression | 
                    Exec expression | 
                    If condition statement statement |
                    Skip
(* Un exemple d'expression *)

(* expr1= (x-10) *)
definition "expr1= (Sub (Variable ''x'') (Constant 10))"


(* Des exemples de programmes *)

(* p1= exec(0) *) (*bad*)
definition "p1= Exec (Constant 0)"


(* p2= {
        print(10)
        exec(0+0)
       }
*)(*bad*)

definition "p2= (Seq (Print (Constant 10)) (Exec (Sum (Constant 0) (Constant 0))))"

(* p3= {
         x:=0
         exec(x)
       }
*)(*bad*)

definition "p3= (Seq (Aff ''x'' (Constant 0)) (Exec (Variable ''x'')))"

(* p4= {
         read(x)
         print(x+1)
       }
*)(*ok*)
definition "p4= (Seq (Read ''x'') (Print (Sum (Variable ''x'') (Constant 1))))"


(* Le type des evenements soit X: execute, soit P: print *)
datatype event= X int | P int

(* les flux de sortie, d'entree et les tables de symboles *)

type_synonym outchan= "event list"
definition "el1= [X 1, P 10, X 0, P 20]"                   (* Un exemple de flux de sortie *)

type_synonym inchan= "int list"           
definition "il1= [1,-2,10]"                                (* Un exemple de flux d'entree [1,-2,10]              *)

type_synonym symTable= "(string * int) list"
definition "(st1::symTable)= [(''x'',10),(''y'',12)]"      (* Un exemple de table de symbole *)


(* La fonction (partielle) de recherche dans une liste de couple, par exemple une table de symbole *)
datatype 'a option= None | Some 'a

fun assoc:: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option"
where
"assoc _ [] = None" |
"assoc x1 ((x,y)#xs)= (if x=x1 then Some(y) else (assoc x1 xs))"

(* Exemples de recherche dans une table de symboles *)

value "assoc ''x'' st1"     (* quand la variable est dans la table st1 *)
value "assoc ''z'' st1"     (* quand la variable n'est pas dans la table st1 *)


(* Evaluation des expressions par rapport a une table de symboles *)
fun evalE:: "expression \<Rightarrow> symTable \<Rightarrow> int"
where
"evalE (Constant s) e = s" |
"evalE (Variable s) e= (case (assoc s e) of None \<Rightarrow> -1 | Some(y) \<Rightarrow> y)" |
"evalE (Sum e1 e2) e= ((evalE e1 e) + (evalE e2 e))" |
"evalE (Sub e1 e2) e= ((evalE e1 e) - (evalE e2 e))" 

(* Exemple d'Ã©valuation d'expression *)

value "evalE expr1 st1"

(* Evaluation des conditions par rapport a une table de symboles *)
fun evalC:: "condition \<Rightarrow> symTable \<Rightarrow> bool"
where
"evalC (Eq e1 e2) t= ((evalE e1 t) = (evalE e2 t))"

(* Evaluation d'un programme par rapport a une table des symboles, a un flux d'entree et un flux de sortie. 
   Rend un triplet: nouvelle table des symboles, nouveaux flux d'entree et sortie *)
fun evalS:: "statement \<Rightarrow> (symTable * inchan * outchan) \<Rightarrow> (symTable * inchan * outchan)"
where
"evalS Skip x=x" |
"evalS (Aff s e)  (t,inch,outch)=  (((s,(evalE e t))#t),inch,outch)" |
"evalS (If c s1 s2)  (t,inch,outch)=  (if (evalC c t) then (evalS s1 (t,inch,outch)) else (evalS s2 (t,inch,outch)))" |
"evalS (Seq s1 s2) (t,inch,outch)= 
    (let (t2,inch2,outch2)= (evalS s1 (t,inch,outch)) in
        evalS s2 (t2,inch2,outch2))" |
"evalS (Read _) (t,[],outch)= (t,[],outch)" |
"evalS (Read s) (t,(x#xs),outch)= (((s,x)#t),xs,outch)" |
"evalS (Print e) (t,inch,outch)= (t,inch,((P (evalE e t))#outch))" |
"evalS (Exec e) (t,inch,outch)= 
  (let res= evalE e t in
   (t,inch,((X res)#outch)))"



(* Exemples d'Ã©valuation de programmes *)
(* Les programmes p1, p2, p3, p4 ont Ã©tÃ© dÃ©finis plus haut *)
(* p1= exec(0) *)

value "evalS p1 ([],[],[])"

(* ------------------------------------ *)
(* p2= {
        print(10)
        exec(0+0)
       }
*)

value "evalS p2 ([],[],[])"

(* ------------------------------------ *)
(* p3= {
         x:=0
         exec(x)
       }
*)

value "evalS p3 ([],[],[])"

(* ------------------------------------ *)
(* p4= {
         read(x)
         print(x+1)
       }
*)

value "evalS p4 ([],[10],[])"


definition "bad1= (Exec (Constant 0))"
definition "bad2= (Exec (Sub (Constant 2) (Constant 2)))"
definition "bad3= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x'')) (Exec (Sub (Variable ''x'') (Constant 1)))))"
definition "bad4= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) Skip (Aff ''y'' (Constant 1))) (Exec (Sum (Variable ''y'') (Constant 1)))))"
definition "bad5= (Seq (Read ''x'') (Seq (Aff ''y'' (Sum (Variable ''x'') (Constant 2))) (Seq (If (Eq (Variable ''x'') (Sub (Constant 0) (Constant 1))) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x'')))) (Seq (Aff ''x'' (Sub (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x''))))) (Exec (Variable ''y'')))))"
definition "bad6= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 1)) (Aff ''z'' (Constant 0))) (Exec (Variable ''z''))))"
definition "bad7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 1))) (Exec (Variable ''z''))))"
definition "bad8= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Variable ''x'') (Variable ''y'')) (Exec (Constant 1)) (Exec (Constant 0)))))"
definition "ok0= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Print (Sum (Variable ''y'') (Variable ''x'')))
(Print (Variable ''x''))
) (Print (Variable ''y''))
) (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 2)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 3)) (Seq (Print (Variable ''x''))
 (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''z'' (Sum (Variable ''x'') (Variable ''x''))) (Aff ''z'' (Sub (Variable ''x'') (Variable ''y'')))) (Print (Variable ''z''))
)))))))))))"
definition "ok1= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Sum (Variable ''x'') (Variable ''x'')))
 (Seq (Exec (Constant 10)) (Seq (Read ''y'') (If (Eq (Variable ''y'') (Constant 0)) (Exec (Constant 1)) (Exec (Constant 2)))))))"
definition "ok2= (Exec (Variable ''y''))"
definition "ok3= (Seq (Read ''x'') (Exec (Sum (Variable ''y'') (Constant 2))))"
definition "ok4= (Seq (Aff ''x'' (Constant 0)) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 20))) (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 4))) (Seq (Exec (Variable ''z'')) (Exec (Variable ''x''))))))"
definition "ok5= (Seq (Read ''x'') (Seq (Aff ''x'' (Constant 4)) (Exec (Variable ''x''))))"
definition "ok6= (Seq (If (Eq (Constant 1) (Constant 2)) (Aff ''x'' (Constant 0)) (Aff ''x'' (Constant 1))) (Exec (Variable ''x'')))"
definition "ok7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (If (Eq (Variable ''x'') (Constant 4)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 1)))) (Exec (Variable ''x''))))"
definition "ok8= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 2))) (Exec (Sub (Variable ''x'') (Constant 3)))))"
definition "ok9= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Sum (Variable ''y'') (Sum (Variable ''y'') (Variable ''x''))))))))"
definition "ok10= (Seq (Read ''x'') (If (Eq (Variable ''x'') (Constant 0)) (Exec (Constant 1)) (Exec (Variable ''x''))))"
definition "ok11= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Sum (Variable ''x'') (Constant 1))) Skip) (Exec (Variable ''x''))))"
definition "ok12= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''z'') (If (Eq (Variable ''z'') (Constant 0)) (Exec (Variable ''y'')) (Exec (Variable ''z'')))))"
definition "ok13= (Seq (Aff ''z'' (Constant 4)) (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (Aff ''x'' (Sum (Variable ''x'') (Sum (Variable ''z'') (Variable ''x'')))) (Seq (Aff ''z'' (Sum (Variable ''z'') (Variable ''x''))) (Seq (If (Eq (Variable ''y'') (Constant 1)) (Aff ''x'' (Sub (Variable ''x'') (Variable ''y''))) Skip) (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Aff ''y'' (Sum (Variable ''y'') (Constant 1))) (Exec (Variable ''x''))) Skip) (Exec (Variable ''y'')))))))))"
definition "ok14= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Variable ''y''))))))"


(* Le TP commence ici! *)
(* TODO: BAD, san0, lemme de correction *)

fun BAD::"(symTable * inchan * outchan) ⇒ bool"
  where
"BAD  (symT, inch, [])   = False " |
"BAD (symT, inch, ((X n)#b)) = (if (n = 0) then True else BAD (symT, inch, b)) " |
"BAD (symT, inch, ((P n)#b)) = BAD (symT, inch, b) " 

value "BAD (evalS p4 ([],[],[]))"

(* programme accepté si pas d'instructions exec *)
fun san1::"statement ⇒ bool"
  where
"san1 (Exec _) = False" |
"san1 (If condition stat1 stat2) = (if (san1 stat1) then (san1 stat2) else False) " |  (* si stat1 est inoffensif on regarde stat2 sinon c'est que stat1 est mauvais donc on rend False *)
"san1 (Seq stat1 stat2)  = (if (san1 stat1) then (san1 stat2) else False) " |
"san1 _ = True" 


(* programme accepté si uniquement des exec sur des constantes non 0 *)
fun san2::"statement ⇒ bool"
  where
"san2 (Exec (Constant n)) = (if (n = 0) then False else True)" |
"san2 (Exec _) = False" |
"san2 (If condition stat1 stat2) = (if (san2 stat1) then (san2 stat2) else False) " | 
"san2 (Seq stat1 stat2)  = (if (san2 stat1) then (san2 stat2) else False) " |
"san2 _ = True" 


datatype typeAbs = Define int | Undefine
type_synonym symTableAbs= "(string * typeAbs) list"

(* addition pour typeAbs *)
fun addAbs:: "typeAbs ⇒ typeAbs ⇒ typeAbs"
  where
"(addAbs  Undefine _ ) = Undefine "|
"(addAbs  _ Undefine ) = Undefine "|
"(addAbs  (Define x) (Define y)) = (Define (x + y)) "

(* soustraction pour typeAbs *)
fun subAbs:: "typeAbs ⇒ typeAbs ⇒ typeAbs"
  where
"(subAbs  Undefine _ ) = Undefine "|
"(subAbs  _ Undefine ) = Undefine "|
"(subAbs  (Define x) (Define y)) = (Define (x - y)) "

(* La fonction (partielle) de recherche dans une table de symbole Abs *)
fun assocAbs:: "string  ⇒ (string * typeAbs) list  ⇒ typeAbs"
where
"assocAbs _ [] = (Define (-1))" |
"assocAbs x1 ((x,y)#xs)= (if (x=x1)  then y  else (assocAbs x1 xs))" 



(* Evaluation des expressions par rapport a une table de symboles Abs *)
fun evalEAbs:: "expression  ⇒ symTableAbs  ⇒ typeAbs"
where
"evalEAbs (Constant s) e = (Define s)" |
"evalEAbs (Variable s) e= (assocAbs s e)" |
"evalEAbs (Sum e1 e2) e= (addAbs (evalEAbs e1 e) (evalEAbs e2 e))" |
"evalEAbs (Sub e1 e2) e= (subAbs (evalEAbs e1 e) (evalEAbs e2 e))" 

(*  permet de comparer 2 typesAbs, si ils sont identiques rend True *)
fun eqAbs::"typeAbs   ⇒ typeAbs  ⇒ bool"
where
"(eqAbs Undefine Undefine) = True" |
"(eqAbs (Define x) (Define y)) = (x=y)" |
"(eqAbs _ _ ) = False"

(* fonction qui permet de comparer 2 typesAbs et rend Define 1 si ils sont Define et égaux aux int  *)
(* (Define 0) correspond  à false et (Define 1) à true *)
fun evalCAbsAux::" typeAbs ⇒ typeAbs  ⇒ typeAbs"
  where
"(evalCAbsAux (Define x) (Define y) ) = (if (x=y) then (Define 1) else (Define 0))" |
"(evalCAbsAux _ _) = Undefine"

(* Evaluation des conditions par rapport a une table de symboles Abs *)
fun evalCAbs:: "condition ⇒ symTableAbs ⇒ typeAbs"   
where
"evalCAbs (Eq e1 e2) t=  (evalCAbsAux (evalEAbs e1 t) (evalEAbs e2 t)) "      


(* parcours d'une table de symbole Abs, rajoute le couple string * typeAbs ou actualise le couple avec le nouveau typeAbs si le string est déjà présent *)
fun affAbs:: "(string * typeAbs)  ⇒ (string * typeAbs) list  ⇒  (string * typeAbs) list  "
where
"affAbs a [] = [a]  " |
"affAbs (x1, y1) ((x,y)#xs) = (if (x=x1)  then ((x1,y1)#xs)  else ((x,y)#(affAbs (x1,y1) xs )))" 


(* permet d'obtenir le bool d'un couple (bool * symTableAbs) *)
fun bCouple:: "(bool * symTableAbs)  ⇒ bool"
  where
"bCouple (b, st) = b"

(* rend True uniquement si le couple est déjà présent dans la table de symbole ou que le typeAbs du couple est Undefine*)
fun presentStAbs:: "(string * typeAbs)   ⇒ symTableAbs   ⇒ bool"
  where
"(presentStAbs (x1, y1) []) = False" | 
"(presentStAbs (x1, Undefine) _ ) = True" |
"(presentStAbs (x1, y1) ((x2, y2)#st)) = (if ((x1=x2) \<and> (eqAbs y1 y2) ) 
                                          then True
                                          else (presentStAbs (x1, y1) st) )" 

(* parcours une list symTableAbs équivalente à (string * typeAbs) list *)
(* et si un élément se trouve dans la seconde list et est Define et identique alors on le rajoute à la symTableAbs résultat *)
(* si l'élément est Undefine on le rajoute aussi *)
(* sinon on rajoute le couple (x, Undefine) à la list resultat *)
fun STunionAux::" symTableAbs   ⇒ symTableAbs   ⇒ symTableAbs  ⇒ symTableAbs "
  where
"(STunionAux [] st stresul) = stresul" |
"(STunionAux  ((x,y)#rest) st stresul) =  (if (presentStAbs (x,y) st) then (STunionAux rest st ((x,y)#stresul)) else  (STunionAux rest st ((x,Undefine)#stresul))) "

(* rend un couple (bool * symTablesAbs) qui est l'union des pires cas de deux couples (bool * symTablesAbs) *)
fun STunion::" (bool * symTableAbs)   ⇒ (bool * symTableAbs)   ⇒ (bool * symTableAbs)"
  where
"(STunion (b1, stAbs1) (b2, stAbs2)) = (if (b1 \<and> b2) then (b1,(STunionAux stAbs2 stAbs1 (STunionAux stAbs1 stAbs2 []))) else  (False,(STunionAux stAbs2 stAbs1 (STunionAux stAbs1 stAbs2 []))))  "


(* à partir d'un programme, permet de remplacer le bool en entrée par défaut à vrai à faux si un exec 0 arrive *)
fun san5::"statement ⇒ ( bool * symTableAbs) ⇒ ( bool * symTableAbs)  "
  where
"(san5 Skip (b, st )) = (b, st) " |
"(san5 (Exec expr)(b, st)) = (if ( (eqAbs (evalEAbs expr st)  Undefine) \<or>  (eqAbs (evalEAbs expr st)(Define 0)))  then (False, st)  else (b,st))" |  (* le programme est accepté uniquement si l'évaluation de l'expression ne rend ni Undefine ni Define 0 *) 
"(san5 (If condition stat1 stat2) (b, st))  = (if (eqAbs  (evalCAbs condition st ) Undefine) 
                                               then (if ((bCouple (san5 stat1 (b, st))) \<and> (bCouple (san5 stat2 (b, st)))) then (STunion (san5 stat1 (b, st)) (san5 stat2 (b, st))  ) else (False, st)) 
                                                else (if (eqAbs (evalCAbs condition st) (Define 1)) then ( san5 stat1 (b, st)) else (san5 stat2 (b, st)))) " |  (* On a 3 cas soit evalCAbs rend Undefine soit Define 0 soit Define 1 *)  (*cas Undefine on doit regarder stat1 et stat2 *)

"(san5 (Seq stat1 stat2) (b, st)) = (if (bCouple (san5 stat1 (b, st))) then (san5 stat2 (san5 stat1 (b, st))) else (False, st)) " |

"(san5 (Print expression) (b, st)) = (b, st)" |

"(san5 (Aff string expression) (b, st)) = (b, (affAbs (string, (evalEAbs expression st)) st))   " |  (* a la table de symbole on rajoute la nouvelle valeur pour string *)

"(san5 (Read string) (b, st)) = (b, (affAbs (string, Undefine) st))"







fun safe::"statement ⇒ bool"
  where
"safe p = (bCouple (san5 p (True, [])))"




value "assoc ''x'' st1"     (* quand la variable est dans la table st1 *)
value "assoc ''z'' st1"     (* quand la variable n'est pas dans la table st1 *)

(* memo




type_synonym symTable= "(string * int) list"

definition "(st24::symTable)= [(''x'',10),(''y'',12)]"      (* Un exemple de table de symbole *)


datatype expression= Constant int | Variable string | Sum expression expression | Sub expression expression

datatype condition= Eq expression expression

datatype statement= Seq statement statement | 
                    Aff string expression | 
                    Read string | 
                    Exec expression | 
*)



value "safe (bad1)"
value "safe (bad2)"
value "safe (bad3)"
value "safe (bad4)"
value "safe (bad5)"
value "safe (bad6)"
value "safe (bad7)"
value "safe (bad8)"

value "safe (ok1)"
value "safe (ok2)"

value "safe p4"








value "BAD (evalS Skip ([],[],[X 0]))"

(* Si san1 accepte un programme alors son Ã©valuation, quelles que soient les entrÃ©es utilisateur (inchan)
   ne provoquera pas d'exec(0) *)
lemma correctionsan1:  "(san1 p) \<longrightarrow> ( \<not>(BAD (evalS p ([] , inchan , [])  )))  "
  nitpick[timeout=120]
  quickcheck[tester=narrowing,size=5,timeout=120]
  apply (induct p)
  apply auto
  sorry


  


(* Si safe accepte un programme alors son Ã©valuation, quelles que soient les entrÃ©es utilisateur (inchan)
   ne provoquera pas d'exec(0) *)
lemma correction: "(safe p) \<longrightarrow> ( \<not>(BAD (evalS p ([] , inchan , [])  ))) "
  nitpick[timeout=120]
  quickcheck[tester=narrowing,size=5,timeout=120]
  sorry


(* Tout programme inoffensif est accepté par l'analyseur *)
lemma completude: " (\<not>(BAD (evalS p ([] , inchan , [])  ))) \<longrightarrow> (safe p) "
  nitpick[timeout=120]
  quickcheck[tester=narrowing,size=5,timeout=120]
  sorry


(* ----- Restriction de l'export Scala (Isabelle 2018) -------*)
(* ! ! !  NE PAS MODIFIER ! ! ! *)
(* Suppression de l'export des abstract datatypes (Isabelle 2018) *)
code_reserved Scala
  expression condition statement 
code_printing
   type_constructor expression \<rightharpoonup> (Scala) "expression"
  | constant Constant \<rightharpoonup> (Scala) "Constant"
  | constant Variable \<rightharpoonup> (Scala) "Variable"
  | constant Sum \<rightharpoonup> (Scala) "Sum"
  | constant Sub \<rightharpoonup> (Scala) "Sub"  

  | type_constructor condition \<rightharpoonup> (Scala) "condition"
  | constant Eq \<rightharpoonup> (Scala) "Eq"

  | type_constructor statement \<rightharpoonup> (Scala) "statement"
  | constant Seq \<rightharpoonup> (Scala) "Seq"
  | constant Aff \<rightharpoonup> (Scala) "Aff"
  | constant Read \<rightharpoonup> (Scala) "Read"
  | constant Print \<rightharpoonup> (Scala) "Print"
  | constant Exec \<rightharpoonup> (Scala) "Exec"
  | constant If \<rightharpoonup> (Scala) "If"
  | constant Skip \<rightharpoonup> (Scala) "Skip"
  | code_module "" \<rightharpoonup> (Scala) 
\<open>// Code generated by Isabelle
package tp67

import utilities.Datatype._
import scala.language.implicitConversions

// automatic conversion of utilities.Datatype.Int.int to Int.int
object AutomaticConversion{ 
	implicit def int2int(i:utilities.Datatype.Int.int):Int.int =
			i match {
			case utilities.Datatype.Int.int_of_integer(i)=>Int.int_of_integer(i)
	}
	
	def bit_cut_integer(k: BigInt): (BigInt, Boolean) =
  (if (k == BigInt(0)) (BigInt(0), false)
    else {
           val (r, s): (BigInt, BigInt) =
             ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
               (k.abs /% l.abs)).apply(k).apply(BigInt(2));
           ((if (BigInt(0) < k) r else (- r) - s), s == BigInt(1))
         })
         
	def char_of_integer(k: BigInt): String.char =
  {
    val (q0, b0): (BigInt, Boolean) = bit_cut_integer(k)
    val (q1, b1): (BigInt, Boolean) = bit_cut_integer(q0)
    val (q2, b2): (BigInt, Boolean) = bit_cut_integer(q1)
    val (q3, b3): (BigInt, Boolean) = bit_cut_integer(q2)
    val (q4, b4): (BigInt, Boolean) = bit_cut_integer(q3)
    val (q5, b5): (BigInt, Boolean) = bit_cut_integer(q4)
    val (q6, b6): (BigInt, Boolean) = bit_cut_integer(q5)
    val a: (BigInt, Boolean) = bit_cut_integer(q6)
    val (_, aa): (BigInt, Boolean) = a;
    String.Chara(b0, b1, b2, b3, b4, b5, b6, aa)
  }
	
  def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
    case (f, Nil) => Nil
    case (f, x :: xs) => f(x) :: map[A, B](f, xs)
  }

	def explodeList(l: List[Char]): List[String.char] ={
       (l.map(c => { val k: Int = c.toInt; if (k < 128) BigInt(k) else sys.error("Non-ASCII character in literal") })).map(a => char_of_integer(a))
    }
	
	def explode(s: String): List[String.char] ={
	    explodeList(s.toCharArray.toList)
	}
	
	// conversion from Scala String to HOL string
  implicit def string2charList(s:String):List[String.char]= explode(s)
  
  // conversion from Scala List[Char] to HOL List[String.char]
  implicit def charList2charList(l:List[Char]):List[String.char]= explodeList(l)
  // conversion of a pair with a Scala List[String] on the first position
  // to an HOL pair with an HOL List[String.char] on first position
	implicit def tupleString2tupleString[T](t:(List[Char],T)):
	    (List[String.char],T)= t match { case (e1,e2) => (charList2charList(e1),e2)}

  // conversion from Isabelle Int.int to Project Int.int
  implicit def int2Dataint(i:Int.int):utilities.Datatype.Int.int =
            i match {
            case Int.int_of_integer(i)=>utilities.Datatype.Int.int_of_integer(i)
    }

   def stringChar2char(x: String.char): Char = {
        x match {
          case String.Chara(x1,x2,x3,x4,x5,x6,x7,x8) => {
            var n = 0;
            n = if (x8) 2*n+1 else 2*n;
            n = if (x7) 2*n+1 else 2*n;
            n = if (x6) 2*n+1 else 2*n;
            n = if (x5) 2*n+1 else 2*n;
            n = if (x4) 2*n+1 else 2*n;
            n = if (x3) 2*n+1 else 2*n;
            n = if (x2) 2*n+1 else 2*n;
            n = if (x1) 2*n+1 else 2*n;
            n.toChar
          }
        }
      }

    // conversion from Isabelle String to Lists of Chars
    implicit def charList2String(l: List[String.char]): List[Char] = {
          l.map(stringChar2char(_))
    } 
}

import AutomaticConversion._
\<close>


(* Directive pour l'exportation de l'analyseur *)

export_code safe in Scala (case_insensitive)

(* file "~/workspace/TP67/src/tp67/san.scala"   (* Ã  adapter en fonction du chemin de votre projet TP67 *)
*)

end