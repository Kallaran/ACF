theory tp5bis
  imports Main 
begin

(* les glob sont les chaînes unix qui utilisent les jokers ?, * et + pour décrire des ensembles de noms *)

(* Définition du type glob (ici nommé pattern) *)
datatype symbol = Char char | Star | Qmark | Plus

type_synonym word= "char list"
type_synonym pattern= "symbol list" 

(* La fonction qui dit si un mot est accepté par un pattern/glob  *)
fun accept::"pattern \<Rightarrow> word \<Rightarrow> bool"
  where
"accept [] [] = True" |
"accept [Star] _ = True" |
"accept [] (_#_) = False" |
"accept ((Char x)#_) [] = False" | 
"accept ((Char x)#r1) (y#r2) = (if x=y then (accept r1 r2) else False)"  |
"accept (Qmark#r1) [] = False" |
"accept (Qmark#r1) (_#r2) = (accept r1 r2)" |
"accept (Plus#r1) [] = False" |
"accept (Plus#r1) (a#r2) = (accept (Star#r1) r2)" |
"accept (Star#r1) [] = (accept r1 [])" |
"accept (Star#r1) (a#r2) = ((accept r1 (a#r2)) \<or> (accept r1 r2) \<or> (accept (Star#r1) r2))"

(* Les caractères en Isabelle/HOL *)
value "(CHR ''a'')"

(* Quelques exemples d'utilisation de la fonction accept *)
value "accept [Star,(Char (CHR ''a''))] [(CHR ''a'')]"
value "accept [Star,(Char (CHR ''a''))] [(CHR ''b''),(CHR ''a'')]"
value "accept [Star,(Char (CHR ''a''))] [(CHR ''a''),(CHR ''b'')]"
value "accept [Star,Star] []"
value "accept [Plus,Star,Star] []"

(* ----------------------------- Votre TP commence ici! ---------------------------------------- *)
fun simplify::"pattern \<Rightarrow> pattern"
  where
"simplify [] = []" |
"simplify [Plus] = [Plus]" |
"simplify [Star] = [Star]" |
"simplify [Qmark] = [Qmark]" |
"simplify [(Char a)] = [(Char a)]" |

"simplify  ((Char a)#r) = ((Char a)#(simplify r))" |
"simplify (Star #(Star#s)) = (simplify (Star#s))" |
"simplify (Plus #(Plus#s)) = (Qmark#(simplify (Plus#s)))" |
"simplify (Qmark#(Qmark#s)) = (Qmark#(simplify (Qmark#s)))" |

"simplify (Plus#(Star#s)) = (simplify (Plus#s))" |
"simplify (Star#(Plus#s)) = (simplify (Plus#s))" |
"simplify (Qmark#(Plus#s)) = (Qmark#(simplify (Plus#s)))" |
"simplify (Plus#(Qmark#s)) = (Plus#(simplify (Qmark#s)))" |
"simplify (Qmark#(Star#s)) = (simplify (Plus#s))" |
"simplify (Star#(Qmark#s)) = (simplify (Plus#s))" |


"simplify (a#(b#c)) = (a#(simplify (b#c)))" 


(* Le lemme de correction de la fonction simplify... Pour le prouver voir les lemmes intermédiaires à définir, plus bas. *)
lemma "(accept (simplify p) w ) = (accept p w) "
  nitpick
  quickcheck [tester=narrowing]
  sorry


(* Le lemme de minimalité dit que le pattern simplifié est le plus petit de tous les
   patterns équivalents. Reformulé ici sous la forme de sa contraposée: s'il existe un pattern 
   plus petit que le pattern simplifié alors il n'est pas équivalent. Il n'est pas équivalent
   si il existe au moins pour lequel l'acceptation par "accept" sera différente. *)

lemma "((length p)< (length (simplify p2))) \<longrightarrow> (\<exists> w. (accept p w) \<noteq> (accept (simplify p2) w))"
 (* La preuve de ce lemme n'est pas demandée. *)
 (* Utiliser le lemme suivant pour trouver des contre-exemples *)
  nitpick
  quickcheck [tester=narrowing]
  oops

(* Pour trouver (efficacement) des contre-exemples sur ce lemme de minimalité, on va limiter 
   la complexité des patterns considérés qu'on nommera "basicPattern" : Ici des patterns 
    avec *, ?, + et uniquement le caractère A *)


fun basicPattern:: "pattern \<Rightarrow> bool"
  where
"basicPattern [] = True" |
"basicPattern ((Char CHR ''A'') # r) = basicPattern r" |
"basicPattern ((Char _) # r) = False" |
"basicPattern (_ # r) = basicPattern r"

(* Le lemme de minimalité pour les basicPatterns *)
lemma "(basicPattern p) \<longrightarrow> ((length p)< (length (simplify p2))) \<longrightarrow> (\<exists> w. (accept p w) \<noteq> (accept (simplify p2) w))"
  quickcheck [tester=narrowing,timeout=00]
   (* nitpick ne trouve que des contre-exemples qui n'en sont pas *)
  oops

(* La directive d'export du code Scala *)
(* A ne pas modifier! *)
code_reserved Scala
  symbol 
code_printing
   type_constructor symbol \<rightharpoonup> (Scala) "Symbol"
   | constant Char \<rightharpoonup> (Scala) "Char"
   | constant Star \<rightharpoonup> (Scala) "Star"
   | constant Plus \<rightharpoonup> (Scala) "Plus"
   | constant Qmark \<rightharpoonup> (Scala) "Qmark"

export_code simplify in Scala


(* Pour prouver le lemme de correction, il vous sera nécessaire de prouver tous ces lemmes intermédiaires! *)

(* Le pattern vide n'accepte que le mot vide *)
lemma acceptVide: "(accept [] w) \<longrightarrow> w=[]"
  oops
  
(* Le seul pattern n'acceptant que le mot vide est le pattern vide *)
lemma acceptVide2: "(\<forall> w. w\<noteq>[] \<longrightarrow> \<not>(accept p w)) \<longrightarrow> p=[]"
  oops

(* Le seul pattern n'acceptant que le langage ? est ? *)
lemma acceptQmark: "(\<forall> w. (accept [Qmark] w = (accept p w))) \<longrightarrow> p=[Qmark]"
  oops

(* Si le pattern commence par un caractère ou un point d'interrogation alors le mot accepté
   commence forcément par un caractère (il ne peut être vide) *)
lemma charAndQmarkRemoval: "((x\<noteq>Star) \<and> (x\<noteq> Plus) \<and> (accept (x#r) m)) \<longrightarrow> (\<exists> x2 r2. m=x2#r2 \<and> (accept r r2))"
  oops
  
(* Si le pattern commence par une étoile, on peut soit l'oublier soit oublier le premier caractère du mot accepté *)
lemma patternStartsWithStar: "((accept (Star#r) m)) \<longrightarrow> ((accept r m) \<or> (\<exists> x2 r2. m=x2#r2 \<and> (accept (Star#r) r2)))"
  oops
    
(* On peut compléter à gauche n'importe quel pattern par une étoile *)
lemma completePatternWithStar: "(accept r m) \<longrightarrow> (accept (Star#r) m)"
  oops
    
lemma completePatternWithStar2: "(accept r m) \<longrightarrow> (accept (Star#r) (m1@m))"
  oops
   

(* On peut oublier une étoile dès qu'il y en a une juste après *)
lemma forgetOneStar:"(accept (Star#(Star#r)) w) = (accept (Star#r) w)"
  oops
  

(* Etoile suivie de point d'interrogation est équivalent à point d'interrogation étoile *)
lemma starQmark:"((accept (Star#(Qmark#r)) w) = (accept (Qmark#(Star#r)) w))"
  oops
  
(* Si deux patterns sont équivalents on peut les compléter à gauche... *)

(* ... par une étoile *)
lemma equivalentPatternStar:"((\<forall> w1. (accept p1 w1) = (accept p2 w1))) \<longrightarrow> ((accept (Star#p1) w) = (accept (Star#p2) w))"
  oops
    
(* ... par un caractère (identique) *)
lemma equivalentPatternChar:"((\<forall> w. (accept p1 w) = (accept p2 w))) \<longrightarrow> ((accept ((Char x)#p1) w) = (accept ((Char x)#p2) w))"
  oops
  
(* ... par un point d'interrogation *)
lemma equivalentPatternQmark:"((\<forall> w. (accept p1 w) = (accept p2 w))) \<longrightarrow> ((accept (Qmark#p1) w) = (accept (Qmark#p2) w))"
  oops
  
(* Par un plus *)
lemma equivalentPatternPlus:"((\<forall> w. (accept p1 w) = (accept p2 w))) \<longrightarrow> ((accept (Plus#p1) w) = (accept (Plus#p2) w))"
  oops
  
lemma plusStarQmark:"((accept (Star#(Qmark#r)) w) = (accept (Plus#r) w))"
  oops
  

lemma plusStarStar:"((accept (Plus#(Star#r)) w) = (accept (Plus#r) w))"
  oops
  

lemma plusPlus1:"((accept (Plus#(Plus#r)) w) = (accept (Qmark#(Plus#r)) w))"
  oops
  
(* Le lemme de correction final *)
lemma correction:""
  oops

  
end
 