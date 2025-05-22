theory ParserImp
  imports Main IMP_CONCUR_MULTI
  keywords "MACHINE" :: thy_decl
     and   "Globals" "Locals" "Thread" "and" "Locks" "limit"
     and "SKIPS" "IF" "THEN" "ELSE" "WHILE" "LOCK" "UNLOCK" "SEND" "REC" "LOCAL" 


begin
(*
ML_file "$ISABELLE_HOME/src/Pure/Syntax/syntax.ML"
ML_file "$ISABELLE_HOME/src/Pure/Isar/token.ML"

setup \<open>
  let
    val keywords = fold Keyword.add_command ["MACHINE", "Globals", "Locals", "Thread", 
      "and", "Locks", "limit", "SKIPS", "IF", "THEN", "ELSE", "WHILE", "LOCK", 
      "UNLOCK", "SEND", "REC", "LOCAL"] Keyword.empty_keywords;
  in
    Context.theory_map (Keyword.update keywords)
  end
\<close>
*)

section \<open>Parser and Term-Reading\<close>
ML\<open>
(*val parse_var_decl = Parse.binding --| Parse.$$$ ":" -- (Parse.position (Parse.term))*)

(* Représentation syntaxique d'un programme *)
datatype com =
    SKIP
  | Assign of string * term
  | Seq of com * com
  | Cond of term * com * com
  | While of term * com
  | Lock of term
  | Unlock of term
  | Send of term * term
  | Rec of string * term

val parse_one_var =
  ((Parse.binding --
  Scan.option (Parse.$$$ "::" |-- Parse.term)   --
  Scan.option (Parse.$$$ "=" |-- Parse.term)) --|
  (Parse.$$$ ";"))
  >> (fn ((name, ty_opt), init_opt) => (name, ty_opt, init_opt ) );

val parse_one_lock = 
  (Parse.binding --|
  Parse.$$$ ";")
  >> (fn name => name) ; (*I*)

val parse_var = Parse.term
val parse_earith = Parse.term
val parse_ebool  = Parse.term
val parse_mv  = Parse.term
val parse_sv = Parse.term


val parse_instr_ref : (Token.T list -> (com * Token.T list)) Unsynchronized.ref =
  Unsynchronized.ref (fn _ => raise Fail "parser not yet initialized")

val parse_instr: (com parser) =
  let
    val parser =
      Parse.!!! (
        Parse.$$$ "SKIPS" >> K SKIP
        || (Parse.$$$ "LOCAL" |-- parse_var --| Parse.$$$ ":=" -- parse_earith --| (Parse.$$$ ";"))
            >> (fn (v, e) => Assign (v, e)))
        || (Parse.$$$ "IF" |-- parse_ebool --| Parse.$$$ "THEN"
            -- Parse.!!! (fn xs => !parse_instr_ref xs) --| Parse.$$$ "ELSE"
            -- Parse.!!! (fn xs => !parse_instr_ref xs)
            --| (Parse.$$$ ";"))
            >> (fn ((b, c1), c2) => Cond (b, c1, c2))
        || (Parse.$$$ "WHILE" |-- parse_ebool --| Parse.$$$ "DO"
            -- Parse.!!! (fn xs => !parse_instr_ref xs)
            --| (Parse.$$$ ";")
            >> (fn (b, c) => While (b, c)))
        || (Parse.$$$ "LOCK" |-- parse_mv  --| (Parse.$$$ ";")>> Lock)
        || (Parse.$$$ "UNLOCK" |-- parse_mv  --| (Parse.$$$ ";")>> Unlock)
        || (parse_sv --| Parse.$$$ "\<hookrightarrow>" -- parse_earith --| (Parse.$$$ ";")
            >> (fn (sv, e) => Send (sv, e)))
        || (parse_var --| Parse.$$$ "\<hookleftarrow>" -- parse_sv --| (Parse.$$$ ";")
            >> (fn (v, sv) => Rec (v, sv)))
            
  in
    (parse_instr_ref := parser; parser);
end

end\<close>


(*val parse_instr_seq = Parse.list1 parse_instr >> (fn cs => foldr1 Seq cs)*)
  (*|| (Parse.$$$ "WHILE" |-- parse_ebool --| Parse.$$$ "DO" -- parse_instr
     >> (fn (b, c) => While (b, c)))
  || (Parse.$$$ "LOCK" |-- parse_mv >> Lock)
  || (Parse.$$$ "UNLOCK" |-- parse_mv >> Unlock)
  || (parse_sv --| Parse.$$$ "\<hookrightarrow>" -- parse_earith
     >> (fn (sv, e) => Send (sv, e)))
  || (parse_var --| Parse.$$$ "\<hookleftarrow>" -- parse_sv
     >> (fn (v, sv) => Rec (v, sv)))*)
(*
val and_thread = 
  \<^keyword>\<open>and\<close> -- (Scan.repeat parse_instr)

val parse_machine_spec = (
          Parse.binding 
       -- \<^keyword>\<open>Globals\<close>       -- (Scan.repeat parse_one_var) (*repeat1 si on impose au moins une variable et un lock*)
       -- \<^keyword>\<open>Locks\<close>      -- (Scan.repeat parse_one_lock)
       -- \<^keyword>\<open>Thread\<close> 
       -- \<^keyword>\<open>Locals\<close>            -- (Scan.repeat1 parse_one_var)
       -- (Scan.repeat parse_instr)
       -- (Scan.repeat and_thread)
       --| \<^keyword>\<open>limit\<close>
  ) *)

(*
fun test_semantics
  ((((((mach, gls), lks), lcls), is), ts), _ ) =
  let
    val _ = writeln ("Machine name: " ^ Binding.name_of mach)
    val _ = writeln ("Locks: " ^ String.concatWith ", " (map Binding.name_of lks))
    val _ = writeln ("Number of global variables: " ^ Int.toString (length gls))
    val _ = writeln ("Number of local variables: " ^ Int.toString (length lcls))
    val _ = writeln ("Number of main instructions: " ^ Int.toString (length is))
    val _ = writeln ("Number of additional threads: " ^ Int.toString (length ts))
  in
    fn thy => thy
  end


fun test_one_var str = 
  let
    val toks = Token.explode (  Thy_Header.get_keywords (Proof_Context.theory_of @{context})) Position.none str
  in let  
    val (res, _) = parse_one_var toks
  in res 
end 
end

val _ = test_one_var "x :: int = 4;"*)
(*
val toks_var = Token.explode (Keyword.temp ()) Position.none "x::nat = 0;";
val (var_result, _) = parse_one_var toks_var;
val _ = writeln (fst var_result); (* devrait afficher "x" *)
*)
(*val _ =
  Outer_Syntax.command 
    \<^command_keyword>\<open>MACHINE\<close>   
    "parses and prints IMP Machine Specification"
    (parse_machine_spec >> (Toplevel.theory o test_semantics))
*)(*
val _ =
  Outer_Syntax.command 
      \<^command_keyword>\<open>MACHINE\<close>   
      "defines IMP Machine Specification"
      (parse_machine_spec) >> context_check >> (Toplevel.theory o semantics));
*)

