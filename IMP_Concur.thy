theory IMP_Concur
  imports Main IMP_CONCUR_MULTI
  keywords "MACHINE" :: thy_decl
     and   "Globals" "Locals" "Thread" "and" "Locks" "limit"
     and "SKIPS" "IF" "THEN" "ELSE" "WHILE" "DO" "LOCAL" "LOCK" "UNLOCK" "STOP"

(*
PROBLEMES:  
Boucle infinie WHILE-IF #Le stop n'est pas reconnu, 
Initialisation locals,
Locals sont des termes pas des bindings,
Initialisation des globals ne marche qu'avec un terme ex x = 5 OK x = 2+3 NOT OK
*)
begin
section \<open>Parser and Term-Reading\<close>
ML\<open>
val parse_var = Parse.name
val parse_earith = Parse.term
val parse_ebool  = Parse.term
val parse_mv  = Parse.term
val parse_sv = Parse.name

val parse_one_var =
  ((Parse.binding --
  Scan.option (Parse.$$$ "::" |-- Parse.term)   --
  Scan.option (Parse.$$$ "=" |-- Parse.term)) --|
  (Parse.$$$ ";"))

val parse_one_lock = 
  (Parse.binding --|
  Parse.$$$ ";")

val parse_local =
  (Parse.term --|
  (Parse.$$$ ";"))

val parse_update =
  ((Parse.position parse_var --| Parse.$$$ "\<hookrightarrow>") -- parse_sv
      >> (fn ((x, _), v) => [ "\<hookrightarrow>", x, v ]))
  || ((Parse.position parse_var --| Parse.$$$ "\<hookleftarrow>") -- parse_mv
      >> (fn ((x, _), v) => [ "\<hookleftarrow>", x, v ]))
  || (\<^keyword>\<open>LOCAL\<close> |-- Parse.position Parse.binding --| Parse.$$$ ":=" -- parse_earith
      >> (fn ((x, _), v) => [ "LOCAL", Binding.name_of x, v ]))

val parse_skip = \<^keyword>\<open>SKIPS\<close> >> (fn _ => ["SKIP"])
val parse_lock =
  \<^keyword>\<open>LOCK\<close> |-- parse_var >> (fn v => [ "LOCK", v ])

val parse_unlock =
  \<^keyword>\<open>UNLOCK\<close> |-- parse_var >> (fn v => [ "UNLOCK", v ]);

val parse_instr_ref : (Token.T list -> (string list * Token.T list)) Unsynchronized.ref =
  Unsynchronized.ref (fn _ => raise Fail "parser not yet initialized")


val parse_cond =                   
  \<^keyword>\<open>IF\<close> |-- ((parse_ebool)) --
  \<^keyword>\<open>THEN\<close> -- (Scan.repeat (fn xs => !parse_instr_ref xs)) --|
  \<^keyword>\<open>ELSE\<close> -- (Scan.repeat (fn xs => !parse_instr_ref xs)) --|
  \<^keyword>\<open>STOP\<close>

   >> (fn ((b, c1), c2) =>
        ["IF", fst b] @ List.concat c1 @ ["ELSE"] @ List.concat c2 @ ["ENDIF"])
 
val parse_while =
  \<^keyword>\<open>WHILE\<close> |--  parse_ebool --
  \<^keyword>\<open>DO\<close> -- Scan.repeat (fn xs => !parse_instr_ref xs)
  --| \<^keyword>\<open>STOP\<close>
   >> (fn (b, body) => ["WHILE", fst b] @ List.concat body @["ENDDO"])

val parse_actions =
  let
    val parser =
      Scan.repeat (
        parse_cond
        || (parse_lock )
        || (parse_unlock )
        || (parse_update)
        || (parse_while)
        || (parse_skip)
      )
      >> List.concat
  in
    (parse_instr_ref := parser; parser)
  end


val parse_thread = (\<^keyword>\<open>Thread\<close> || \<^keyword>\<open>and\<close>)
                 -- \<^keyword>\<open>Locals\<close> |-- (Scan.repeat parse_local)
                 -- parse_actions
                 >> (fn (l, a) =>
                        ["THREAD", "LOCALS"] @ (l) @ ["ACTIONS"]@ a )





val parse_machine_spec = (
          Parse.binding 
       -- \<^keyword>\<open>Globals\<close>       -- (Scan.repeat parse_one_var)
       -- \<^keyword>\<open>Locks\<close>      -- (Scan.repeat parse_one_lock)
       -- (Scan.repeat parse_thread)
       -- \<^keyword>\<open>limit\<close>
      )
(*
val context_check = K I

val _ =
  Outer_Syntax.command 
      \<^command_keyword>\<open>MACHINE\<close>   
      "defines Machine Specification"
      (parse_machine_spec >> context_check >> I);
*)
val _ =
  Outer_Syntax.command
    \<^command_keyword>\<open>MACHINE\<close>
    "defines Event-B Machine Specification"
    (parse_machine_spec >> (fn x =>
      (Output.writeln (@{make_string} x); Toplevel.theory I)));


\<close>

MACHINE Machine
Globals x :: int = 5; y;
Locks z; l;
Thread
  Locals u;
and 
Locals test;
limit


end

(*
theory IMP_Concur
  imports Main IMP_CONCUR_MULTI
  keywords "MACHINE" :: thy_decl
     and   "Globals" "Locals" "Thread" "and" "Locks" "limit"
     and "SKIPS" "IF" "THEN" "ELSE" "WHILE" "DO" "LOCAL" "LOCK" "UNLOCK" "STOP"


begin
section \<open>Parser and Term-Reading\<close>
ML\<open>
val parse_var = Parse.name
val parse_earith = Parse.term
val parse_ebool  = Parse.term
val parse_mv  = Parse.term
val parse_sv = Parse.name

val parse_one_var =
  ((Parse.binding --
  Scan.option (Parse.$$$ "::" |-- Parse.term)   --
  Scan.option (Parse.$$$ "=" |-- Parse.term)) --|
  (Parse.$$$ ";"))

val parse_one_lock = 
  (Parse.binding --|
  Parse.$$$ ";")

val parse_local =
  (Parse.term --|
  (Parse.$$$ ";"))

val parse_update =
  ((Parse.position parse_var --| Parse.$$$ "\<hookrightarrow>") -- parse_sv
      >> (fn ((x, _), v) => [ "\<hookrightarrow>", x, v ]))
  || ((Parse.position parse_var --| Parse.$$$ "\<hookleftarrow>") -- parse_mv
      >> (fn ((x, _), v) => [ "\<hookleftarrow>", x, v ]))
  || (\<^keyword>\<open>LOCAL\<close> |-- Parse.position Parse.binding --| Parse.$$$ ":=" -- parse_earith
      >> (fn ((x, _), v) => [ "LOCAL", Binding.name_of x, v ]))

val parse_skip = \<^keyword>\<open>SKIPS\<close> >> (fn _ => ["SKIP"])
val parse_lock =
  \<^keyword>\<open>LOCK\<close> |-- parse_var >> (fn v => [ "LOCK", v ])

val parse_unlock =
  \<^keyword>\<open>UNLOCK\<close> |-- parse_var >> (fn v => [ "UNLOCK", v ]);

val parse_instr_ref : (Token.T list -> (string list * Token.T list)) Unsynchronized.ref =
  Unsynchronized.ref (fn _ => raise Fail "parser not yet initialized")


val parse_cond =                   
  \<^keyword>\<open>IF\<close> |-- (parse_ebool) --
  \<^keyword>\<open>THEN\<close> -- (Scan.repeat (!parse_instr_ref)) --|
  \<^keyword>\<open>ELSE\<close> -- (Scan.repeat (!parse_instr_ref)) --|
  \<^keyword>\<open>STOP\<close>

   >> (fn ((b, c1), c2) =>
       (parse_instr_ref:= Unsynchronized.ref (fn _ => raise Fail "parser not yet initialized");
       ["IF", fst b] @ List.concat c1 @ ["ELSE"] @ List.concat c2 @ ["ENDIF"]))
 
val parse_while =
  \<^keyword>\<open>WHILE\<close> |--  parse_ebool --
  \<^keyword>\<open>DO\<close> -- Scan.repeat  (!parse_instr_ref)
  --| \<^keyword>\<open>STOP\<close>
   >> (fn (b, body) => ["WHILE", fst b] @ List.concat body @["ENDDO"])

val parse_actions =
      Scan.repeat (
        parse_cond
        || (parse_lock )
        || (parse_unlock )
        || (parse_update)
        || (parse_while)
        || (parse_skip)
      )
      >> List.concat

val _ = parse_instr_ref := parse_actions


val parse_thread = (\<^keyword>\<open>Thread\<close> || \<^keyword>\<open>and\<close>)
                 -- \<^keyword>\<open>Locals\<close> |-- (Scan.repeat parse_local)
                 -- parse_actions
                 >> (fn (l, a) =>
                        ["THREAD", "LOCALS"] @ (l) @ ["ACTIONS"]@ a )





val parse_machine_spec = (
          Parse.binding 
       -- \<^keyword>\<open>Globals\<close>       -- (Scan.repeat parse_one_var)
       -- \<^keyword>\<open>Locks\<close>      -- (Scan.repeat parse_one_lock)
       -- (Scan.repeat parse_thread)
       -- \<^keyword>\<open>limit\<close>
      )
(*
val context_check = K I

val _ =
  Outer_Syntax.command 
      \<^command_keyword>\<open>MACHINE\<close>   
      "defines Machine Specification"
      (parse_machine_spec >> context_check >> I);
*)
val _ =
  Outer_Syntax.command
    \<^command_keyword>\<open>MACHINE\<close>
    "defines Event-B Machine Specification"
    (parse_machine_spec >> (fn x =>
      (Output.writeln (@{make_string} x); Toplevel.theory I)));


\<close>

MACHINE Machine
Globals x :: int = 4; y;
Locks z; l;
Thread
  Locals u;
and 
Locals test;
(*WHILE A DO SKIPS STOP;*)
(*IF A THEN SKIPS ELSE SKIPS STOP*)
LOCK 5 
SKIPS
limit


end
*)