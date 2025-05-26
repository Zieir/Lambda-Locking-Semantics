theory IMP_CONCUR_parse
  imports Main (*IMP_CONCUR_MULTI_CSPM*)
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
                    locals_decl : ((binding * typ) * term option) list ,
                    actions     : a_term list,
                    locstab         : (term option) Symtab.table
                   }
type absy = {system          : binding,
             globals_decls   : (binding * typ * Position.T * term option) list,
             varstab         : (term option) Symtab.table,
             locks_decls     : (binding * term * Position.T) list,
             threads_decls   : thread_absy list
            }


val SPY = Unsynchronized.ref(NONE:absy option)
val SPYG= Unsynchronized.ref([Bound 0])

fun pre_const ((bdg, typ), _) = (bdg, typ, NoSyn)
fun pre_const' (b, trm) = (b,   fastype_of trm, Mixfix.NoSyn) 
fun pre_const_bar (b, trm, _) = (Binding.suffix_name "'" b,  
                                  fastype_of trm, Mixfix.NoSyn) 
fun pre_const2 (b, typ, _, _) = (b,  typ, Mixfix.NoSyn) 
fun pre_const3 (b, trm, _) = (b, fastype_of trm, Mixfix.NoSyn) 

fun pre_event (b, trm, _) = (b, fastype_of trm --> pre_event_type, 
                                   Mixfix.NoSyn)  





fun read_term_err thy msg bind str = 
        let val pos = Position.here(Binding.pos_of bind)
        in  (Syntax.read_term_global thy str
             handle ERROR s => error("error in "^msg^" :"^ pos ^"\n"^ s ) ) 
        end

fun read_term_err_pos thy msg _ str pos = 
        (Syntax.read_term_global thy str
             handle ERROR s => error("error in "^msg^" :"^ (Position.here pos) ^"\n"^ s ) ) 
        
fun check_thread thy thy3 (((SOME thread_name, locals_opt), actions_list): raw_thread_absy) =
  let
    fun loc_decls_conv ((bdg, (s, pos)), SOME init_term) =
          let 
            val typ = Syntax.read_typ_global thy s
            val inferred_type = fastype_of init_term
            val ctxt = Proof_Context.init_global thy
            val inferred_str = Syntax.string_of_typ ctxt inferred_type
            val declared_str = Syntax.string_of_typ ctxt typ
          in
            if inferred_type <> typ then
              error ("Type mismatch in variable " ^ Binding.name_of bdg ^
                     ": expected " ^ declared_str ^ ", but got " ^ inferred_str)
            else
              ((bdg, typ), SOME init_term)
          end
        | loc_decls_conv ((bdg, (s, pos)), NONE) =
          ((bdg, Syntax.read_typ_global thy s), NONE)

    fun action_conv Skip = SkipA
      | action_conv (Assign (bdg, str)) = AssignA (bdg, read_term_err thy "assignment" bdg str)
      | action_conv (Lock b) = LockA b
      | action_conv (Unlock b) = UnlockA b
      | action_conv (Send (b, str)) = SendA (b, read_term_err thy "send value" b str)
      | action_conv (Receive (b, str)) = ReceiveA (b, read_term_err thy "receive value" b str)
      | action_conv (Ifelse ((cond_str, then_branch), else_branch)) =
          let
            val cond_term = read_term_err thy "if condition" (Binding.name "if_cond") cond_str
          in
            IfelseA ((cond_term, map action_conv then_branch), map action_conv else_branch)
          end
      | action_conv (While (cond_str, body)) =
          let
            val cond_term = read_term_err thy "while condition" (Binding.name "while_cond") cond_str
          in
            WhileA (cond_term, map action_conv body)
          end
        val (loc_decls', thy3') = case locals_opt of
            NONE => ([], thy3)
          | SOME locals =>
              let
                val locals_terms = map (fn ((bdg,(s,pos)), init_opt_str) =>
                   let
                     val init_opt_term = case init_opt_str of
                         NONE => NONE
                       | SOME str => SOME (read_term_err thy "local init" bdg str)
                   in
                     ((bdg, (s,pos)), init_opt_term)
                   end) locals
        
                val decls = map loc_decls_conv locals_terms
                val thy4 = Sign.add_consts (map pre_const decls) thy3
              in
                (decls, thy4)
              end

    fun conv_decl_init ((n, _), init_opt) = (Binding.name_of n, init_opt)
    val locstab'     = Symtab.make (map conv_decl_init loc_decls')
    val actions' = map action_conv actions_list
  in
    { nom_thread = thread_name, locals_decl = loc_decls', actions = actions', locstab = locstab' }
  end
  | check_thread _ _ ((NONE, _), _) =
      error "Current syntax restriction: event must have label."



(**)
val context_check = fn (((system: binding , 
                          globals :  ((binding * (string * Position.T)) * string option)list),
                          locks :  (binding * (string * Position.T)) list),
                          threads : raw_thread_absy list)
                           =>
                     fn thy : theory => 
                     let val read = read_term_err thy
                         fun global_decls_conv ((bdg, (s, pos)), SOME init_term) =
                            let 
                              val typ = Syntax.read_typ_global thy s
                              val inferred_type = fastype_of init_term
                              val ctxt = Proof_Context.init_global thy
                              val inferred_str = Syntax.string_of_typ ctxt inferred_type
                              val declared_str = Syntax.string_of_typ ctxt typ
                            in
                              if inferred_type <> typ then
                                error ("Type mismatch in variable " ^ Binding.name_of bdg ^
                                       ": expected " ^ declared_str ^ ", but got " ^ inferred_str)
                              else
                                (bdg, typ, pos, SOME init_term)
                            end
                          | global_decls_conv ((bdg, (s, pos)), NONE) =
                            (bdg, Syntax.read_typ_global thy s, pos, NONE)
                     val (global_decls', thy3') = 
                                  let
                                    val global_terms = map (fn ((bdg,(s,pos)), init_opt_str) =>
                                       let
                                         val init_opt_term = case init_opt_str of
                                             NONE => NONE
                                           | SOME str => SOME (read_term_err thy "local init" bdg str)
                                       in
                                         ((bdg, (s,pos)), init_opt_term)
                                       end) globals
                            
                                    val decls = map global_decls_conv global_terms
                                    val thy4 = Sign.add_consts (map pre_const2 decls) thy
                                  in
                                    (decls, thy4)
                                  end


                        (* val global_decls' =  map (fn ((b, (str,pos)), init) =>(
                                                     if init = NONE then
                                                          (b ,read "var_type" b str ,pos ,NONE)  
                                                     else 
                                                          (b ,read "var_type" b str ,pos ,SOME(read "var_init" b (the init)))  
                                                    )) globals;*)
                         fun conv_decl_init (n,_, _  , init_opt) = (Binding.name_of n, init_opt)
                         val varstab     = Symtab.make (map conv_decl_init global_decls')
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
(*fun read_typing thy s = 
  let val t = Syntax.read_typ thy s
  in t end

fun check_init_typ thy (init_term : term) (expected_typ : typ) =
  let val ty_init = try Typing.infer_type thy init_term handle _ => error "Cannot infer type of init"
  in
    if ty_init = expected_typ then ()
    else error ("Type mismatch in initialization: expected " ^ Syntax.string_of_typ thy expected_typ ^ 
                " but got " ^ Syntax.string_of_typ thy ty_init)
  end

val global_decls' = map (fn ((b, (typ_str,pos)), init_opt) =>
    let
      val typ_term = Syntax.read_typ thy typ_str
      val typ_val = typ_term (* en théorie typ_term est un typ déjà *)
      val _ = case init_opt of
          NONE => ()
        | SOME init_str =>
            let
              val init_term = Syntax.read_term_global thy init_str
              val _ = check_init_typ thy init_term typ_val
            in () end
    in
      (b, typ_val, pos, init_opt)
    end
  ) globals;*)

section‹Semantic Check›
ML‹

fun define_THREADS machine thread_decls (lthy : local_theory) = ()

fun semantics (absy_cl: theory -> absy) (thy : theory) =()

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
          val _ = Output.writeln "=== CONTEXT CHECKING ==="
          val checked = context_check x thy
          val _ = Output.writeln (@{make_string} checked)
        in
          thy
        end)))
›


SYSTEM WellTypedSys
  globals v:‹bool› = ‹True› x:‹bool› = False
  locks   l:‹()›                                       
  thread t1 :
         any var1:‹nat› = ‹4 :: nat›      
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
  globals v :nat= ‹4::nat›
  locks   l: nat
  (*thread t :
       any var_local:‹()›
       actions SKIP; LOCK 4;
        v->5;
  end;*)
  thread m:
       any var_local :int = ‹4 :: int›
       actions SKIP;
       LOCK 4;
       x = ‹(4+5) :: int›;
      IF ‹4+5 == 4› THEN 
              WHILE x DO 
              LOCK 5; 
              UNLOCK 4;DONE 
           ELSE
        SKIP;DONE
  end;
end;

                
end
