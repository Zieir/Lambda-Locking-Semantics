theory Lambda_Viewer
  imports Main
begin

ML \<open>
(* Contexte de travail *)
val ctxt = Proof_Context.init_global @{theory};

(* Lire un terme logique depuis une chaîne *)
fun parse_term str = Syntax.read_term ctxt str

(* Obtenir le type d'un terme *)
fun type_of_term t = Term.type_of t

(* Pretty-printer explicite pour \<lambda>-termes *)
fun show_term (Const (name, _)) = name
  | show_term (Free (name, _)) = name
  | show_term (Bound i) = "B." ^ Int.toString i
  | show_term (Abs (x, _, body)) = "\<lambda>" ^ x ^ ". " ^ show_term body
  | show_term (t1 $ t2) = "(" ^ show_term t1 ^ " " ^ show_term t2 ^ ")"
  | show_term _ = "<complex>"

(* Fonction principale *)
fun analyze str =
  let
    val t = parse_term str
    val ty = type_of_term t
    val _ = tracing ("Input: " ^ str)
    val _ = tracing ("Lambda form: " ^ show_term t)
    val _ = tracing ("Type: " ^ Syntax.string_of_typ ctxt ty)
  in () end;

(* 🔁 Tests *)
val _ = analyze "x + y"
val _ = analyze "x < y \<longrightarrow> P x"
val _ = analyze "map f xs"
val _ = analyze "\<lambda>x. x + 1"
\<close>

end
