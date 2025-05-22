theory IMP_CONCUR_parse
  imports IMP_CONCUR_MULTI_CSPM
  keywords  "SYSTEM" :: thy_decl
      and   "globals" "locks" "LOCK" "UNLOCK" "thread" "WHILE" "IF" "ELSE" "THEN"
           "end;" "any" "actions" "DO" "<-" "->" "SKIP" "DONE"
 
begin

section \<open>Parser and Term-Reading\<close>

ML\<open> 

val quiet_mode = false

fun message quiet_mode s = if quiet_mode then () else writeln s;

datatype ('a, 'b) sum = inl of 'a | inr of 'b;

local open HOLogic in

fun map_opt f _ (SOME a) = f a
   |map_opt _ a NONE = a

fun map_option f  = map_opt (SOME o f) NONE

(* remove this > *)
fun map_option f (SOME a) = SOME(f a)
   |map_option _ NONE = NONE



(* declaration de variables  v:\<open>N\<close> := \<open>5::int\<close> ou v:<N>*)
val parse_var_decl = (Parse.binding --| Parse.$$$ ":" -- (Parse.position (Parse.term)))
                   -- (Scan.option ( Parse.$$$ "=" |-- Parse.term))
                    : ((binding*(string*Position.T))*string option) parser

(*declarations de locks*)
val parse_locks = Parse.binding --| Parse.$$$ ":" -- (Parse.position (Parse.term)) 
                  : (binding*(string*Position.T)) parser


datatype a = Skip
            | Assign of binding*string 
            | Unlock of binding 
            | Lock of binding
            | Send of binding*string 
            | Receive of binding*string
            | Ifelse of (string*(a list))*(a list) 
            | While of string*(a list)

val parse_lock = \<^keyword>\<open>LOCK\<close> |-- Parse.binding --| Parse.$$$ ";"
                 >> (fn (x) => Lock(x))
                  : a parser
val parse_unlock =  \<^keyword>\<open>UNLOCK\<close> |-- Parse.binding --| Parse.$$$ ";"
                 >>  (fn (x) => Unlock(x))
                  : a parser
val parse_assign = Parse.binding --| Parse.$$$ "=" -- Parse.term --| Parse.$$$ ";"
                >> (fn (x) => Assign(x))
                  : a parser
val parse_send = Parse.binding --| \<^keyword>\<open>->\<close> -- Parse.term --| Parse.$$$ ";"
                 >> (fn (x) => Send(x))
                  : a parser
val parse_receive = Parse.binding --| \<^keyword>\<open><-\<close> -- Parse.term --| Parse.$$$ ";"
                >> (fn (x) => Receive(x))
                  : a parser
val parse_skip = \<^keyword>\<open>SKIP\<close> |-- Parse.$$$ ";"
                >> (fn _  => Skip) : a parser

fun parse_actions TL   =( Scan.repeat1 ( parse_lock 
                                  || parse_unlock 
                                  || parse_assign
                                  || parse_send 
                                  || parse_receive
                                  || parse_skip
                                  || parse_if_else 
                                  || parse_while 
                                  )) TL
and  parse_if_else TL = ((\<^keyword>\<open>IF\<close> |-- Parse.term --| \<^keyword>\<open>THEN\<close>
                    -- parse_actions --| \<^keyword>\<open>ELSE\<close> -- parse_actions--| \<^keyword>\<open>DONE\<close>)
                    >>(fn (x) => Ifelse(x))) TL
and parse_while TL =(( \<^keyword>\<open>WHILE\<close> |-- Parse.term --| \<^keyword>\<open>DO\<close> -- parse_actions --|\<^keyword>\<open>DONE\<close>)
                    >> (fn (x) => While(x))) TL


                                

(*thread T1 : where var_local_decl
             actions  action1;
                       ... ;
                      actionN;
  end;
  thread T2: actions  action1;
                       ... ;
                      actionN;
  end; *)
val parse_threads =( \<^keyword>\<open>thread\<close> |-- (Scan.option (Parse.binding)) --| Parse.$$$ ":"
                                      -- (Scan.option (\<^keyword>\<open>any\<close> |--  Scan.repeat1 (parse_var_decl) ))
                                     -- (\<^keyword>\<open>actions\<close> |-- parse_actions)
                                     --| \<^keyword>\<open>end;\<close>)

type raw_absy =  (((binding (*system name*)
            *
             ((binding * (string * Position.T)) * string option)list) (*globals*)
            *
            (binding * (string * Position.T)) list) (*locks*)
           *
           ((binding option * (*a thread's name*)
             ((binding * (string * Position.T)) *string option)list option) (*a thread's locals*)
            *
              a list (*a thread's actions*)
           ) list) (*threads lists*)

val parse_system_spec = (
          Parse.binding 
       --| \<^keyword>\<open>globals\<close>    -- (Scan.repeat1 parse_var_decl)
       --| \<^keyword>\<open>locks\<close>      -- (Scan.repeat1 parse_locks)
       -- (Scan.repeat1 parse_threads)
       --| \<^keyword>\<open>end;\<close>
      ) : raw_absy parser

end
\<close>



section\<open>Context Checking\<close>
ML\<open>

fun check_thread thy thy3 ((SOME thread_name,inl ((ex_decls,guard_decls),action_decls))) = 
    let fun ex_decls_conv (bdg, (s, _)) = (bdg, read_term_err thy "transition variable" bdg s)
        val ex_decls'        = map ex_decls_conv ex_decls
        val thy3             = Sign.add_consts (map pre_const' ex_decls') thy3
        fun guard_decl_conv (SOME bdg, (s, pos)) = (bdg, read_term_err thy3 "guard" bdg s)
        fun action_decl_conv (SOME bdg, (s, pos)) = (bdg, read_term_err thy3 "action" bdg s)
        val guard_decls'     = map guard_decl_conv guard_decls
        val action_decls'    = map action_decl_conv action_decls
    in
        (trans_name, inl ({exists = ex_decls', guards = guard_decls',actions = action_decls'}))
    end
   | check_thread thy thy3 (NONE, _)            = 
          error"Current syntax restriction: event must have label."
   | check_thread thy thy3 (SOME trans_name, inr(inl X)) = 
          (warning"Current syntax restriction: event variant not supported."; (trans_name,inr(inl X)))
   | check_thread thy thy3 (SOME trans_name, inr(inr X)) = 
          (warning"Current syntax restriction: event variant not supported."; (trans_name,inr(inr X)))



\<close>










section\<open>Impression\<close>
ML\<open>

(*effet de bord sur output: imprime x*)
val context_check = (fn x:raw_absy => fn y => (Toplevel.keep (fn _ => Output.writeln (@{make_string} x));y))

(*
val _ =
  Outer_Syntax.command 
      \<^command_keyword>\<open>SYSTEM\<close>   
      "defines Event-B Machine Specification"
      (parse_system_spec >> context_check >> (Toplevel.theory o I));
*)


val _ =
  Outer_Syntax.command
    \<^command_keyword>\<open>SYSTEM\<close>
    "defines Event-B Machine Specification"
    (parse_system_spec >> (fn x =>
      (Output.writeln (@{make_string} x); Toplevel.theory I)));


\<close>
SYSTEM S
  globals v:\<open>N\<close>= 4 x:\<open>K\<close> = True
  locks   l:\<open>()\<close>                                       
  thread t :
       any var_local:\<open>()\<close>
       actions SKIP; LOCK 4;
        v->5;
  end;
  thread :
       any var_local:\<open>()\<close>
       actions SKIP;
       LOCK 4;
       x = \<open>"4+5"\<close>;
      IF x THEN 
              WHILE x DO 
              LOCK 5; 
              UNLOCK 4;DONE 
           ELSE
        SKIP;DONE
  end;
end;
                
end
