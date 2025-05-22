theory IMP_CONCUR_MULTI_CSPM
  imports Main HOL.String IMP_CONCUR_MULTI
begin

fun string_of_nat :: "nat \<Rightarrow> string"
where
  "string_of_nat n = (if n < 10 then [char_of (48 + n)] else 
     string_of_nat (n div 10) @ [char_of (48 + (n mod 10))])"

definition string_of_int :: "int \<Rightarrow> string"
where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"

(* Collecte des canaux utilisés dans un programme com *)
fun collect :: "com \<Rightarrow> string list" where
   "collect SKIP = []"
  |" collect (Assign v _) = [''assign_'' @ v]"
  |"collect (Seq c1 c2) = collect c1 @ collect c2"
  |" collect (Cond _ c1 c2) = collect c1 @ collect c2 @ [''guard'', ''guard_not'']"
  |" collect (While _ c) = collect c @ [''guard'', ''guard_not'']"
  |" collect (Lock m) = [''lock_'' @ string_of_int m]"
  |" collect (Unlock m) = [''unlock_'' @ string_of_int m]"
  |" collect (Send ch _) = [''send_'' @ string_of_int m]"
  |" collect (Rec _ ch) = [''recv_'' @ string_of_int m]"

ML \<open>
(* Machinerie de traduction IMP_concur vers CSPm *)


(*
(* Déclarations de canaux CSPm *)
fun mk_channel_decl chs =
  let val uniq = rev (distinct (rev chs))
      fun mk_line c = "channel " ^ c ^ " : Int\n"
  in String.concat (map mk_line uniq) end

(* Traduction d'une expression arithmétique simple *)
fun translate_expr e =
    (* ici on suppose e est (\<lambda>\<sigma>. k) *)
    Int.toString (case e of f => f dummy_state_local)

(* Traduction de com vers DSL CSPm *)
fun cspm_of SKIP = "SKIP"
  | cspm_of (Assign v e) =
      "assign_" ^ v ^ "!" ^ translate_expr e ^ " -> SKIP"
  | cspm_of (Seq c1 c2) =
      let val p1 = cspm_of c1
          val p2 = cspm_of c2
      in "(" ^ p1 ^ " ; " ^ p2 ^ ")" end
  | cspm_of (Cond b c1 c2) =
      let val p1 = cspm_of c1
          val p2 = cspm_of c2
      in "(guard -> " ^ p1 ^ " [] guard_not -> " ^ p2 ^ ")" end
  | cspm_of (While b c) =
      let val p = cspm_of c
      in "mu X • (guard -> (" ^ p ^ " ; X) [] guard_not -> SKIP)" end
  | cspm_of (Lock m) = "lock_" ^ Int.toString m ^ " -> SKIP"
  | cspm_of (Unlock m) = "unlock_" ^ Int.toString m ^ " -> SKIP"
  | cspm_of (Send ch e) = "send_" ^ Int.toString ch ^ "!" ^ translate_expr e ^ " -> SKIP"
  | cspm_of (Rec v ch) = "recv_" ^ Int.toString ch ^ "?" ^ v ^ " -> SKIP"

(* Génération du fichier CSPm *)
val _ =
  let
    val prog = @{term "prog1 :: com"}  (* AST de prog1 importé *)
    val chs  = collect prog
    val decl = mk_channel_decl chs
    val body = "MAIN = " ^ cspm_of prog
    val content = decl ^ "\n" ^ body ^ "\n\nassert MAIN :[ deadlock free ]\n"
    val out = TextIO.openOut "ImpConcurModel.csp"
  in
    TextIO.output (out, content);
    TextIO.closeOut out;
    writeln "Generated ImpConcurModel.csp"
  end
*)

\<close>

end