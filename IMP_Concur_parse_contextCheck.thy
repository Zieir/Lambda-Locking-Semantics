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
val parse_skip = \<^keyword>‹SKIP› |-- Parse.$$$ ";"
                >> (fn _  => Skip) : a parser

fun parse_actions TL   =( Scan.repeat ( parse_lock 
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
val parse_threads =( \<^keyword>‹thread› |-- (Scan.option (Parse.binding)) --| Parse.$$$ ":"
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

type raw_thread_absy = (binding option * (*a thread's name*)
                       ((binding * (string * Position.T)) *string option)list option)* (*a thread's locals*)
                        a list (*a thread's actions*)
                     

val parse_system_spec = (
          Parse.binding 
       --| \<^keyword>‹globals›    -- (Scan.repeat1 parse_var_decl)
       --| \<^keyword>‹locks›      -- (Scan.repeat1 parse_locks)
       -- (Scan.repeat1 parse_threads)
       --| \<^keyword>‹end;›
      ) : raw_absy parser

end
›


typedecl pre_event_type

section‹Context Checking›
ML‹
val pre_event_type = @{typ ‹pre_event_type›}

datatype a_term = SkipA
            | AssignA of binding*term 
            | UnlockA of binding 
            | LockA of binding
            | SendA of binding*term 
            | ReceiveA of binding*term
            | IfelseA of (term*(a_term list))*(a_term list) 
            | WhileA of term*(a_term list)

type thread_absy = {nom_thread  : binding ,
                    locals_decl : ((binding * term) * term option) list ,
                    actions     : a_term list
                   }
type absy = {system          : binding,
             globals_decls   : (binding * term * Position.T * term option) list,
             varstab         : (term * Position.T) Symtab.table,
             locks_decls     : (binding * term * Position.T) list,
             threads_decls   : thread_absy list
            }


val SPY = Unsynchronized.ref(NONE:absy option)
val SPYG= Unsynchronized.ref([Bound 0])

fun pre_const ((b, trm), _) = (b,  fastype_of trm, Mixfix.NoSyn) 
fun pre_const' (b, trm) = (b,   fastype_of trm, Mixfix.NoSyn) 
fun pre_const_bar (b, trm, _) = (Binding.suffix_name "'" b,  
                                  fastype_of trm, Mixfix.NoSyn) 
fun pre_const2 (b, trm, _, _) = (b,  fastype_of trm, Mixfix.NoSyn) 
fun pre_const3 (b, trm, _) = (b, fastype_of trm, Mixfix.NoSyn) 

fun pre_event (b, trm, _) = (b, fastype_of trm --> pre_event_type, 
                                   Mixfix.NoSyn)  





fun read_term_err thy msg bind str = 
        let val pos = Position.here(Binding.pos_of bind)
        in  (Syntax.read_term_global thy str
             handle ERROR s => error("error in "^msg^" :"^ pos ^"\n"^ s ) ) 
        end

fun read_term_err_pos thy msg bind str pos = 
        (Syntax.read_term_global thy str
             handle ERROR s => error("error in "^msg^" :"^ (Position.here pos) ^"\n"^ s ) ) 
        
fun check_thread thy thy3 (((SOME thread_name, SOME locals_list) , actions_list): raw_thread_absy) =
    let fun loc_decls_conv ((bdg, (s, pos)), SOME init_str) =
            let 
              val typ_term = read_term_err_pos thy "variable type" bdg s pos
              val init_term = read_term_err_pos thy "initial value" bdg init_str pos
            in
              ((bdg, typ_term), SOME init_term)
            end
        | loc_decls_conv ((bdg, (s, pos)), NONE) =
            ((bdg, read_term_err thy "variable type" bdg s), NONE)

        val loc_decls'        = map loc_decls_conv locals_list
        val thy3             = Sign.add_consts (map pre_const loc_decls') thy3
        (*val initial_values = 
            List.mapPartial (fn ((b, _), SOME t) => SOME (b, t) | _ => NONE) loc_decls'*)

        fun action_conv (Skip) = (SkipA)
          | action_conv (Assign (bdg, str)) =
              (AssignA (bdg, read_term_err thy "assignment" bdg str))
          | action_conv (Lock b) = LockA b
          | action_conv (Unlock b) = UnlockA b
          | action_conv (Send (b, str)) =
              SendA (b, read_term_err thy "send value" b str)
          | action_conv (Receive (b, str)) =
              ReceiveA (b, read_term_err thy "receive value" b str)
          | action_conv (Ifelse ((cond_str, then_branch), else_branch)) =
              let val cond_term = read_term_err thy "if condition" (Binding.name "if_cond") cond_str
              in IfelseA ((cond_term, map (action_conv) then_branch), map (action_conv) else_branch) end
          
          | action_conv (While (cond_str, body)) =
              let val cond_term = read_term_err thy "while condition" (Binding.name "while_cond") cond_str
              in WhileA (cond_term, map (action_conv) body) end
        val actions'        = map action_conv actions_list

    in
       {nom_thread = thread_name, locals_decl= loc_decls', actions = actions' }
    end
   | check_thread _ _ ((NONE,_) ,_)                                 = 
          error"Current syntax restriction: event must have label."
   | check_thread thy _ ((SOME thread_name, NONE) , actions_list)      =
     let fun action_conv (Skip) = (SkipA)
          | action_conv (Assign (bdg, str)) =
              (AssignA (bdg, read_term_err thy "assignment" bdg str))
          | action_conv (Lock b) = LockA b
          | action_conv (Unlock b) = UnlockA b
          | action_conv (Send (b, str)) =
              SendA (b, read_term_err thy "send value" b str)
          | action_conv (Receive (b, str)) =
              ReceiveA (b, read_term_err thy "receive value" b str)
          | action_conv (Ifelse ((cond_str, then_branch), else_branch)) =
              let val cond_term = read_term_err thy "if condition" (Binding.name "if_cond") cond_str
              in IfelseA ((cond_term, map (action_conv) then_branch), map (action_conv) else_branch) end
          
          | action_conv (While (cond_str, body)) =
              let val cond_term = read_term_err thy "while condition" (Binding.name "while_cond") cond_str
              in WhileA (cond_term, map (action_conv) body) end
        val actions'        = map action_conv actions_list

    in
       {nom_thread = thread_name, locals_decl= [], actions = actions' }
    end

val context_check = fn (((system: binding , 
                          globals :  ((binding * (string * Position.T)) * string option)list),
                          locks :  (binding * (string * Position.T)) list),
                          threads : raw_thread_absy list)
                           =>
                     fn thy : theory => 
                     let val read = read_term_err thy
                         val global_decls' =  map (fn ((b, (str,pos)), init) =>(
                                                     if init = NONE then
                                                          (b ,read "var_type" b str ,pos ,NONE)  
                                                     else 
                                                          (b ,read "var_type" b str ,pos ,SOME(read "var_init" b (the init)))  
                                                    )) globals;
                         fun conv_decl (n, a, b, _) = (Binding.name_of n, (a, b))
                         val varstab     = Symtab.make (map conv_decl global_decls')
                         val lock_decls'= map (fn (b, (str,pos)) => (b, read "lock_decl" b str, pos)) locks
                         val thy'        = Sign.add_consts (map pre_const2 global_decls') thy
                         val thy''       = thy' |> Sign.add_consts (map pre_event lock_decls')

                         val threads' = map (check_thread thy thy'') threads 
                        val res = {system = system,
                                   globals_decls = global_decls',
                                   varstab = varstab,
                                   locks_decls = lock_decls',
                                   threads_decls = threads'}
                     in  SPY:=(SOME (res)); res end


›





section‹Impression›
ML‹
(*
val _ =
  Outer_Syntax.command 
      \<^command_keyword>‹SYSTEM›   
      "defines Event-B Machine Specification"
      (parse_system_spec >> context_check >> (Toplevel.theory o (K I)));

*)
(*
val _ =
  Outer_Syntax.command
    \<^command_keyword>‹SYSTEM›
    "defines Event-B Machine Specification"
    (parse_system_spec >> (fn x =>
      (Output.writeln (@{make_string} x); Toplevel.theory I)));
*)

val _ =
  Outer_Syntax.command
    \<^command_keyword>‹SYSTEM›
    "defines Event-B Machine Specification"
    (parse_system_spec >> (fn x =>
      Toplevel.theory (fn thy =>
        let
          val _ = Output.writeln "=== PARSED SYSTEM ==="
          val _ = Output.writeln (@{make_string} x)
          val _ = Output.writeln "=== TYPE CHECKING ==="
          val checked = context_check x thy
        in
          thy
        end)))
›
SYSTEM WellTypedSys
  globals v:‹int› = ‹4 › x:‹bool set› = True
  locks   l:‹unit set›                                       
  thread t1 :
       actions 
         SKIP;
         LOCK l;
         v -> 7;
         UNLOCK l;
         IF x THEN 
            WHILE x DO 
              LOCK l; 
              UNLOCK l;
            DONE 
         ELSE
            SKIP;
         DONE
  end;
end;

SYSTEM S
  globals v:‹int›= 4
  locks   l: l                                       
  thread t :
       any var_local:‹()›
       actions SKIP; LOCK 4;
        v->5;
  end;
  thread l :
       any var_local:‹()›
       actions SKIP;
       LOCK 4;      
       x = ‹42+3/8›;
      IF x THEN 
              WHILE x DO 
              LOCK 5; 
              UNLOCK 4;DONE 
           ELSE
        SKIP;DONE
  end;
end;

                
end
