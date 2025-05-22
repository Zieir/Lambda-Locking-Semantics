theory IMP_CONCUR_parse
  imports IMP_CONCUR_MULTI_CSPM
  keywords  "SYSTEM" :: thy_decl
      and   "globals" "locks" "LOCK" "UNLOCK" "thread" "WHILE" "IF" "ELSE" "THEN"
           "end;" "any" "actions" "DO" "<-" "->" "SKIP" "DONE"
 
begin

section ‹Parser and Term-Reading›

ML‹ 

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



(* declaration de variables  v:‹N› := ‹5::int› ou v:<N>*)
val parse_var_decl = (Parse.binding --| Parse.$$$ ":" -- (Parse.position (Parse.term)))
                   -- (Scan.option ( Parse.$$$ "=" |-- Parse.term))
                    : ((binding*(string*Position.T))*string option) parser

(*declarations de locks*)
val parse_locks = Parse.binding --| Parse.$$$ ":" -- (Parse.position (Parse.term)) 
                  : (binding*(string*Position.T)) parser


(*
 actions =
    SKIP ;
  | Assign var Earith ;        
  | IF Cond THEN actions ELSE actions ;
  | WHILE con DO actions ;
  | LOCK t ;                  
  | UNLOCK t ;                
  | Send t Earith ;     
  | Rec var t ;
*)

datatype a = Skip
            | Assign of binding*string 
            | Unlock of binding 
            | Lock of binding
            | Send of binding*string 
            | Receive of binding*string
            | Ifelse of (string*(a list))*(a list) 
            | While of string*(a list)

val parse_lock = \<^keyword>‹LOCK› |-- Parse.binding --| Parse.$$$ ";"
                 >> (fn (x) => Lock(x))
                  : a parser
val parse_unlock =  \<^keyword>‹UNLOCK› |-- Parse.binding --| Parse.$$$ ";"
                 >>  (fn (x) => Unlock(x))
                  : a parser
val parse_assign = Parse.binding --| Parse.$$$ "=" -- Parse.term --| Parse.$$$ ";"
                >> (fn (x) => Assign(x))
                  : a parser
val parse_send = Parse.binding --| \<^keyword>‹->› -- Parse.term --| Parse.$$$ ";"
                 >> (fn (x) => Send(x))
                  : a parser
val parse_receive = Parse.binding --| \<^keyword>‹<-› -- Parse.term --| Parse.$$$ ";"
                >> (fn (x) => Receive(x))
                  : a parser
val parse_skip = \<^keyword>‹SKIP› |-- Parse.$$$ ";" >> (fn _  => Skip) : a parser

fun parse_actions TL   =( Scan.repeat1 ( parse_lock 
                                  || parse_unlock 
                                  || parse_assign
                                  || parse_send 
                                  || parse_receive
                                  || parse_skip
                                  || parse_if_else 
                                  || parse_while 
                                  )) TL
and  parse_if_else TL = ((\<^keyword>‹IF› |-- Parse.term --| \<^keyword>‹THEN›
                    -- parse_actions --| \<^keyword>‹ELSE› -- parse_actions--| \<^keyword>‹DONE›)
                    >>(fn (x) => Ifelse(x))) TL
and parse_while TL =(( \<^keyword>‹WHILE› |-- Parse.term --| \<^keyword>‹DO› -- parse_actions --|\<^keyword>‹DONE›)
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
val parse_threads =( \<^keyword>‹thread› |-- (Scan.option (Parse.binding --| Parse.$$$ ":"))
                                      -- (Scan.option (\<^keyword>‹any› |--  Scan.repeat1 (parse_var_decl) ))
                                     -- (\<^keyword>‹actions› |-- parse_actions)
                                     --| \<^keyword>‹end;›)

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
       --| \<^keyword>‹globals›    -- (Scan.repeat1 parse_var_decl)
       --| \<^keyword>‹locks›      -- (Scan.repeat1 parse_locks)
       -- (Scan.repeat1 parse_threads)
       --| \<^keyword>‹end;›
      ) : raw_absy parser

end
›

ML‹

(*effet de bord sur output: imprime x*)
val context_check = (fn x:raw_absy => fn y => (Toplevel.keep (fn _ => Output.writeln (@{make_string} x));y))

(*
val _ =
  Outer_Syntax.command 
      \<^command_keyword>‹SYSTEM›   
      "defines Event-B Machine Specification"
      (parse_system_spec >> context_check >> (Toplevel.theory o I));
*)


val _ =
  Outer_Syntax.command
    \<^command_keyword>‹SYSTEM›
    "defines Event-B Machine Specification"
    (parse_system_spec >> (fn x =>
      (Output.writeln (@{make_string} x); Toplevel.theory I)));


›


SYSTEM S
  globals v:‹N›= 4 x:‹K›
  locks   l:‹()›
  thread t :
       any var_local:‹()›
       actions SKIP; LOCK 4;
        v->5;
  end;
  thread tu :
       actions SKIP;
       LOCK 4;
       x = 4;
      WHILE x DO LOCK 5; UNLOCK 4;DONE
      IF x THEN SKIP; ELSE SKIP;DONE
  end;
end;
                
end
