theory Church_Translator
  imports Main
begin
 
(* === 1. Langage source ML simplifié === *)

datatype ml_const = CBool bool | CNat nat

datatype ml_expr =
    Var string
  | Lam string ml_expr
  | App ml_expr ml_expr
  | Let string ml_expr ml_expr
  | Const ml_const
  | Add ml_expr ml_expr
  | If ml_expr ml_expr ml_expr


(* === 2. Lambda-calcul de Church === *)

datatype church =
    CVar string
  | CLam string church
  | CApp church church


(* === 3. Constantes de Church === *)

fun church_nat :: "nat \<Rightarrow> church" where
  "church_nat n = 
     CLam ''f'' (CLam ''x'' (foldr (\<lambda>_. CApp (CVar ''f'')) (replicate n ()) (CVar ''x'')))"

definition church_true :: church where
  "church_true \<equiv> CLam ''t'' (CLam ''f'' (CVar ''t''))"

definition church_false :: church where
  "church_false \<equiv> CLam ''t'' (CLam ''f'' (CVar ''f''))"

definition church_succ :: church where
  "church_succ \<equiv> 
     CLam ''n'' (CLam ''f'' (CLam ''x'' 
       (CApp (CVar ''f'') (CApp (CApp (CVar ''n'') (CVar ''f'')) (CVar ''x'')))))"

definition church_plus :: church where
  "church_plus \<equiv> 
     CLam ''m'' (CLam ''n'' (CLam ''f'' (CLam ''x'' 
       (CApp (CApp (CVar ''m'') (CVar ''f'')) 
             (CApp (CApp (CVar ''n'') (CVar ''f'')) (CVar ''x''))))))"

definition church_if :: church where
  "church_if \<equiv> CLam ''b'' (CLam ''t'' (CLam ''e'' 
     (CApp (CApp (CVar ''b'') (CVar ''t'')) (CVar ''e''))))"

definition church_iszero :: church where
  "church_iszero \<equiv> 
     CLam ''n'' (CApp (CApp (CVar ''n'') (CLam ''x'' church_false)) church_true)"


(* === 4. Traduction ML vers Church === *)

fun translate_const :: "ml_const \<Rightarrow> church" where
  "translate_const (CBool True) = church_true"
| "translate_const (CBool False) = church_false"
| "translate_const (CNat n) = church_nat n"

fun translate :: "ml_expr \<Rightarrow> church" where
  "translate (Var x) = CVar x"
| "translate (Lam x e) = CLam x (translate e)"
| "translate (App e1 e2) = CApp (translate e1) (translate e2)"
| "translate (Let x e1 e2) = CApp (CLam x (translate e2)) (translate e1)"
| "translate (Const c) = translate_const c"
| "translate (Add e1 e2) = 
     CApp (CApp church_plus (translate e1)) (translate e2)"
| "translate (If b e1 e2) = 
     CApp (CApp (CApp church_if (translate b)) (translate e1)) (translate e2)"


(* === 5. Évaluation (normalisation) du lambda-calcul Church === *)

fun subst :: "string \<Rightarrow> church \<Rightarrow> church \<Rightarrow> church" where
  "subst x s (CVar y) = (if x = y then s else CVar y)"
| "subst x s (CLam y e) = 
     (if x = y then CLam y e else CLam y (subst x s e))"
| "subst x s (CApp e1 e2) = CApp (subst x s e1) (subst x s e2)"

fun beta :: "church \<Rightarrow> church option" where
  "beta (CApp (CLam x e1) e2) = Some (subst x e2 e1)"
| "beta (CApp e1 e2) = (
     case beta e1 of
       Some e1' \<Rightarrow> Some (CApp e1' e2)
     | None \<Rightarrow> (case beta e2 of
         Some e2' \<Rightarrow> Some (CApp e1 e2')
       | None \<Rightarrow> None))"
| "beta (CLam x e) = (case beta e of Some e' \<Rightarrow> Some (CLam x e') | None \<Rightarrow> None)"
| "beta _ = None"

fun size :: "church \<Rightarrow> nat" where
  "size (CVar _)     = 1"
| "size (CLam _ e)   = Suc (size e)"
| "size (CApp e1 e2) = Suc (size e1 + size e2)"



lemma beta_decr: "beta e = Some e' \<Longrightarrow> size e' < size e"
proof (induction e arbitrary: e')
  case (CVar x)
  then show ?case by simp
next
  case (CLam x e)
  then show ?case
    by (cases "beta e") (auto simp: size.simps)
next
  case (CApp e1 e2)
  then show ?case
  proof (cases rule: beta.cases[of "CApp e1 e2" e'])
    -- “\<beta>-réduction sur un redex à la racine” :
  case (1 x t s)
    (* on sait alors que e = CApp (CLam x t) s et e' = subst x s t *)
  then show ?thesis by (simp add: size_subst_less)

    -- “\<beta>-réduction dans la partie gauche” :
  next
  case (2 e1' e2)
    (* on sait que beta e1 = Some e1' et e' = CApp e1' e2 *)
  then show ?thesis
    by (simp add: size.simps intro: CApp.IH)

    -- “\<beta>-réduction dans la partie droite” :
  next
  case (3 e1 e2')
    (* on sait que beta e2 = Some e2' et e' = CApp e1 e2' *)
  then show ?thesis
    by (simp add: size.simps intro: CApp.IH)
  qed
 


function normalize :: "church \<Rightarrow> church" where
  "normalize e = (case beta e of
     Some e' \<Rightarrow> normalize e'
   | None   \<Rightarrow> e)"
  by pat_completeness auto


section \<open>Tests\<close>

text \<open>Traduction d’une addition 2 + 3 en Church\<close>
value "translate (Add (Const (CNat 2)) (Const (CNat 3)))"
(* Attendu : CApp (CApp church_plus (church_nat 2)) (church_nat 3) *)

text \<open>Normalisation de plus 2 3\<close>
value "normalize (CApp (CApp church_plus (church_nat 2)) (church_nat 3))"
(* Attendu : CLam ''f'' (CLam ''x'' (CApp (CVar ''f'') (CApp (CVar ''f'') (CApp (CVar ''f'') (CApp (CVar ''f'') (CApp (CVar ''f'') (CVar ''x'))))))) 
   soit \<lambda>f.\<lambda>x. f (f (f (f (f x)))) *)

text \<open>Test de l’opérateur if\<close>
value "translate (If (Const (CBool True)) (Const (CNat 1)) (Const (CNat 0)))"
(* Attendu : CApp (CApp (CApp church_if church_true) (church_nat 1)) (church_nat 0) *)

text \<open>Normalisation d’un if false then 1 else 0\<close>
value "normalize (translate (If (Const (CBool False)) (Const (CNat 1)) (Const (CNat 0))))"
(* Attendu : CLam ''f'' (CLam ''x'' (CVar ''x''))   i.e. zéro de Church *)

text \<open>Successeur de 2\<close>
value "normalize (CApp church_succ (church_nat 2))"
(* Attendu : church_nat 3 *)

text \<open>IsZero sur 0 et 1\<close>
value "normalize (CApp church_iszero (church_nat 0))"  (* true  *)
value "normalize (CApp church_iszero (church_nat 1))"  (* false *)

end 


(*
proof (induction e arbitrary: e')
  case (CVar x)
  (* beta (CVar _) = None, donc ce cas n’arrive jamais *)
  then show ?case by simp
next
  case (CLam x e)
  (* beta (CLam x e) = map_option (CLam x) (beta e) *)
  then show ?case
    by (cases "beta e") (auto simp: size.simps)
next
  case (CApp e1 e2)
  (* on réécrit le corps de beta pour ce constructeur *)
  have beta_CApp:
    "beta (CApp e1 e2) =
       (case beta e1 of
          Some e1' \<Rightarrow> Some (CApp e1' e2)
        | None \<Rightarrow> case beta e2 of
                    Some e2' \<Rightarrow> Some (CApp e1 e2')
                  | None    \<Rightarrow> None)"
    by simp
  then show ?case
  proof (cases "beta e1")
    case (Some e1')
    with CApp.IH[of e1'] beta_CApp Some
    show ?thesis by simp
  next
    case None
    then have step2: "beta (CApp e1 e2) = (case beta e2 of Some e2' \<Rightarrow> Some (CApp e1 e2') | None \<Rightarrow> None)"
      using beta_CApp by simp
    then show ?thesis
    proof (cases "beta e2")
      case (Some e2')
      with CApp.IH[of e2'] None step2 show ?thesis by simp
    next
      case None
      with step2 CApp.prems show ?thesis by simp
    qed
  qed
qed

termination
  apply (relation "measure size")
  apply (rule beta_decr)
  done*)


(*theory Church_Translator
  imports Main
begin

ML \<open>
(* Lambda-calcul Church *)
datatype church =
    CVar of string
  | CLam of string * church
  | CApp of church * church

(* Affichage *)
fun show_church (CVar x) = x
  | show_church (CLam (x, body)) = "\<lambda>" ^ x ^ ". " ^ show_church body
  | show_church (CApp (f, x)) = "(" ^ show_church f ^ " " ^ show_church x ^ ")"

(* Contexte global *)
val ctxt = Proof_Context.init_global @{theory}

(* Environment avec définitions *)
fun short_name s = List.last (String.tokens (fn c => c = #".") s)

fun lookup_church s =
  case short_name s of
      "0" => SOME (CLam ("f", CLam ("x", CVar "x")))
    | "1" => SOME (CLam ("f", CLam ("x", CApp (CVar "f", CVar "x"))))
    | "+" => SOME (CLam ("m", CLam ("n", CLam ("f", CLam ("x",
                  CApp (CApp (CVar "m", CVar "f"),
                        CApp (CApp (CVar "n", CVar "f"), CVar "x")))))))
    
    | x => SOME (CVar x)

(* Traduction d’un terme Isabelle vers lambda Church *)
fun term_to_church (Free (name, _)) = the (lookup_church name)
  | term_to_church (Const (name, _)) = the (lookup_church name)
  | term_to_church (t1 $ t2) =
      CApp (term_to_church t1, term_to_church t2)
  | term_to_church (Abs (x, _, body)) =
      CLam (x, term_to_church body)
  | term_to_church _ = CVar "<?>"


fun expand (CVar x) =
      (case lookup_church x of
         SOME body => expand body
       | NONE => CVar x)
  | expand (CApp (f, x)) = CApp (expand f, expand x)
  | expand (CLam (v, body)) = CLam (v, expand body)

(* Test : x + y *)
val t = Syntax.read_term ctxt "x + y"
val c = term_to_church t
val expanded = expand c
val _ = tracing ("Expanded Church: " ^ show_church expanded)
(*val _ = tracing ("Church term: " ^ show_church c)*)

\<close>
ML<
datatype test = 
  Stest of int
  |Stesst of string

>
end
*)