(*<*)theory IMP_CONCUR_parse
  imports Main  (*"HOL-CSPM.CSPM"*) "IMP_CONCUR_sem" (*Isabelle_DOF.technical_report IMP_CONCUR_MULTI_CSPM*)
  keywords  "SYSTEM" :: thy_decl
      and   "globals" "locks" "LOCK" "UNLOCK" "thread" "WHILE" "IF" "ELSE" "THEN"
           "end;" "any" "actions" "DO" "<-" "->" "SKIP" "DONE"
 
begin


section ‹Parser and Term-Reading›

ML‹ 

val quiet_mode = false

fun message quiet_mode s = if quiet_mode then () else writeln s;

datatype ('a, 'b) sum = inl of 'a | inr of 'b;

exception Undeclared_Variable of string

local open HOLogic in

fun map_opt f _ (SOME a) = f a
   |map_opt _ a NONE = a

fun map_option f  = map_opt (SOME o f) NONE

(* remove this *)
fun map_option f (SOME a) = SOME(f a)
   |map_option _ NONE = NONE



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
            | Receive of binding*binding
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
val parse_receive = Parse.binding --| \<^keyword>‹<-› -- Parse.binding --| Parse.$$$ ";"
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
   thread T2: actions  action1;
                       ... ;
                      actionN;
 *)
val parse_threads =( \<^keyword>‹thread› |-- (Scan.option (Parse.binding)) --| Parse.$$$ ":"
                                      -- (Scan.option (\<^keyword>‹any› |--  Scan.repeat1 (parse_var_decl) ))
                                     -- (\<^keyword>‹actions› |-- parse_actions))

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
            | ReceiveA of binding*binding
            | IfelseA of (term*(a_term list))*(a_term list) 
            | WhileA of term*(a_term list)
            |SeqA of a_term * a_term

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


(* Got replaced but would be cool to know why isn't it working

fun check_vars term varstab locstab =
  let
    val vars = Term.add_free_names term []
    fun is_declared v = Symtab.defined varstab v orelse Symtab.defined locstab v
    val undeclared = List.filter (not o is_declared) vars
  in
    if null undeclared then ()
    else error ("Undeclared variable(s) used: " ^ String.concatWith ", " undeclared)
  end*)


fun read_term_err thy msg bind str = 
        let val pos = Position.here(Binding.pos_of bind)
        in  (Syntax.read_term_global thy str
             handle ERROR s => error("error in "^msg^" :"^ pos ^"\n"^ s ) ) 
        end

fun read_term_err_pos thy msg _ str pos = 
        (Syntax.read_term_global thy str
             handle ERROR s => error("error in "^msg^" :"^ (Position.here pos) ^"\n"^ s ) ) 

(* Utilitaire pour lire un terme à partir d’un string *)
fun get_term_and_vars thy str =
  let
    val ctxt = Proof_Context.init_global thy
    val term = Syntax.read_term ctxt str
    val vars = Term.add_free_names term []
  in
    (term, vars)
  end

(* Résout une variable selon priorité locale ou globale *)
fun resolve_var prefer_global var locstab varstab =
  let
    val loc = Symtab.lookup locstab var
    val global = Symtab.lookup varstab var
  in
    if prefer_global then
      (case global of
         SOME (SOME t) => SOME t
       | _ => (case loc of
                 SOME (SOME t) => SOME t
               | _ => NONE))
    else
      (case loc of
         SOME (SOME t) => SOME t
       | _ => (case global of
                 SOME (SOME t) => SOME t
               | _ => NONE))
  end

(* Variante stricte qui renvoie une erreur si non trouvé *)
fun resolve_var_strict prefer_global var locstab varstab =
  case resolve_var prefer_global var locstab varstab of
    SOME t => t
  | NONE => error ("Variable "^var^" non déclarée")

fun check_thread thy thy3 vars_tab (((SOME thread_name, locals_opt), actions_list): raw_thread_absy) =
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
                     ": expected " ^ declared_str ^ ", but got " ^ inferred_str ^ "at " ^ Position.here pos )
            else
              ((bdg, typ), SOME init_term)
          end
        | loc_decls_conv ((bdg, (s, pos)), NONE) =
          ((bdg, Syntax.read_typ_global thy s), NONE)

    fun action_conv _ _ Skip = SkipA
      | action_conv _ _ (Lock b) = LockA b
      | action_conv _ _ (Unlock b) = UnlockA b
      | action_conv varstab locstab (Assign (bdg, str)) =
           let
              val (term, vars) = get_term_and_vars thy str
              val assign_term = term
             val _ =
              if Symtab.defined locstab (Binding.name_of bdg) 
                 orelse Symtab.defined varstab (Binding.name_of bdg)
              then ()
              else error ("Variable " ^ (Binding.name_of bdg) ^ " is not declared (in assign binding)")
            in
              AssignA (bdg, assign_term)
            end


      | action_conv varstab locstab (Send (b, str)) =
          let
            val (term, _) = get_term_and_vars thy str
            val _ =
              if Symtab.defined locstab (Binding.name_of b) 
                 orelse Symtab.defined varstab (Binding.name_of b)
              then ()
              else error ("Variable " ^ (Binding.name_of b) ^ " is not declared (in send)")
          in
            SendA (b, term)
          end

      | action_conv varstab locstab (Receive (blv, bsv)) =
        let
           val _ =
              if Symtab.defined locstab (Binding.name_of blv)
                 then   if (Symtab.defined varstab (Binding.name_of bsv)) then ()
                        else error ("Variable " ^ (Binding.name_of bsv) ^ " is not declared (in receive binding)")
              else error ("Variable " ^ (Binding.name_of blv) ^ " is not declared (in receive binding)")
        in
          ReceiveA (blv, bsv)
        end

      | action_conv varstab locstab (Ifelse ((cond_str, then_branch), else_branch)) =
          let
          val (term, vars) = get_term_and_vars thy cond_str
          val cond_term = term
          val then_branch' = map (action_conv varstab locstab) then_branch
          val else_branch' = map (action_conv varstab locstab) else_branch
        in
          IfelseA ((cond_term, then_branch'), else_branch')
        end

      | action_conv varstab locstab (While (cond_str, body)) =
          let
            val (term, vars) = get_term_and_vars thy cond_str
           (* val cond_term =
              case vars of
                [x] => resolve_var_strict false x locstab varstab
              | _ => term*)
            val cond_term =  term  
            val actions = map (action_conv varstab locstab) body
          in
            WhileA (cond_term, actions)
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
    val actions' = map (action_conv vars_tab locstab') actions_list  in
    { nom_thread = thread_name, locals_decl = loc_decls', actions = actions', locstab = locstab' }
  end
  | check_thread _ _ _ ((NONE, _), _) =
      error "Current syntax restriction: threads must have label."




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
                                       ": expected " ^ declared_str ^ ", but got " ^ inferred_str ^  
                                       "at " ^Position.here pos)
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

                         fun conv_decl_init (n,_, _  , init_opt) = (Binding.name_of n, init_opt)
                         val varstab     = Symtab.make (map conv_decl_init global_decls')
                         val lock_decls'= map (fn (b, (str,pos)) => (b, read "lock_decl" b str, pos)) locks
                         val thy'        = Sign.add_consts (map pre_const2 global_decls') thy
                         val thy''       = thy' |> Sign.add_consts (map pre_event lock_decls')

                         val threads' = map (check_thread thy thy'' varstab) threads 
                        val res = {system = system,
                                   globals_decls = global_decls',
                                   varstab = varstab,
                                   locks_decls = lock_decls',
                                   threads_decls = threads'}
                     in  SPY:=(SOME (res)); res end


›


section‹Semantic Check›
ML‹
(* Redéfinir les types de base de la sémantique *)
type SV = string  (* Shared Variables *)
type V = string   (* Thread-Local Variables *)  
type MV = int     (* Mutex IDs *)
type D = int      (* Data type - simplifié à int *)

type state = string -> int

fun safe_lookup var state =
  case state var of
    ~1 => raise Undeclared_Variable var
  | v => v

type arith_expr = state -> int
type bool_expr = state -> bool

datatype com = 
    SKIP
  | Assign of string * arith_expr
  | Seq of com * com  
  | Cond of bool_expr * com * com
  | While of bool_expr * com
  | Lock of string
  | Unlock of string
  | Store of arith_expr * string
  | Load of string * string

(* Table de mapping pour les locks *)
val lock_table = Unsynchronized.ref (Symtab.empty : int Symtab.table)
val lock_counter = Unsynchronized.ref 0

fun get_lock_id (lock_name : string) : int =
  case Symtab.lookup (!lock_table) lock_name of
    SOME id => id
  | NONE => 
      let 
        val new_id = !lock_counter
        val _ = lock_counter := new_id + 1
        val _ = lock_table := Symtab.update (lock_name, new_id) (!lock_table)
      in 
        new_id 
      end

(* Évaluation des termes Isabelle/HOL *)
fun eval_term_to_int (thy : theory) (term : term) (state : state) : int =
  let
    (* Fonction récursive pour évaluer les termes *)
    fun eval t =
      case t of
        Const (@{const_name "Groups.plus_class.plus"}, _) $ t1 $ t2 =>
          (eval t1) + (eval t2)
      | Const (@{const_name "Groups.minus_class.minus"}, _) $ t1 $ t2 =>
          (eval t1) - (eval t2)
      | Const (@{const_name "Groups.times_class.times"}, _) $ t1 $ t2 =>
          (eval t1) * (eval t2)
      | Const (@{const_name "HOL.Trueprop"}, _) $ t1 => eval t1
      | @{term "0::nat"} => 0
      | @{term "1::nat"} => 1
      | Free (name, _) => safe_lookup name state
      | Bound i =>  i (* Placeholder pour les variables liées *)
      | _ => 
          (* Essayer d'extraire les constantes numériques *)
          (case try (HOLogic.dest_number #> snd) t of
            SOME n => n
          | NONE => 0) (* Valeur par défaut *)
  in
    eval term
  end

fun eval_term_to_bool (thy : theory) (term : term) (state : state) : bool =
  let
    fun eval t =
      case t of
        @{term "True"} => true
      | @{term "False"} => false
      | Const (@{const_name "HOL.conj"}, _) $ t1 $ t2 =>
          (eval t1) andalso (eval t2)
      | Const (@{const_name "HOL.disj"}, _) $ t1 $ t2 =>
          (eval t1) orelse (eval t2)
      | Const (@{const_name "HOL.Not"}, _) $ t1 =>
          not (eval t1)
      | Const (@{const_name "HOL.eq"}, _) $ t1 $ t2 =>
          (eval_term_to_int thy t1 state) = (eval_term_to_int thy t2 state)
      | Const (@{const_name "Orderings.ord_class.less"}, _) $ t1 $ t2 =>
          (eval_term_to_int thy t1 state) < (eval_term_to_int thy t2 state)
      | Const (@{const_name "Orderings.ord_class.less_eq"}, _) $ t1 $ t2 =>
          (eval_term_to_int thy t1 state) <= (eval_term_to_int thy t2 state)
      | Free (name, _) => 
          (case try (fn () => safe_lookup name state) () of
            SOME 0 => false
          | SOME _ => true
          | NONE => false)
      | _ => error ("Unsupported boolean expression: " ^ Pretty.string_of (Syntax.pretty_term_global thy t) )
                                                         (*Syntax.string_of_term_global thy t)*)
  in
    eval term
  end
(* Fixed record pattern matching *)
(*fun process_absy absy_data =
  let
    val {system, globals_decls, locks_decls, threads_decls, varstab} = absy_data
  in
    (* Process the fields *)
    (system, globals_decls, locks_decls, threads_decls)
  end
*)
(* Fonction de conversion de l'AST vers com *)
fun convert_to_com (thy : theory) (actions : a_term list) 
                   (varstab : (term option) Symtab.table) 
                   (locstab : (term option) Symtab.table) : com =
  let
    fun term_to_arith_expr (t : term) : arith_expr = 
      fn state => eval_term_to_int thy t state
    
    fun term_to_bool_expr (t : term) : bool_expr =
      fn state => eval_term_to_bool thy t state
    
    fun convert_action (action : a_term) : com =
      case action of
        SkipA => SKIP
      | AssignA (bdg, term) => 
        let
          val name = Binding.name_of bdg
          val is_local = Symtab.defined locstab name
        in
          if is_local
          then Assign (name, term_to_arith_expr term)  (* local *)
          else Store (term_to_arith_expr term, name)   (* global *)
        end
      | LockA bdg => 
          Lock (Binding.name_of bdg)
      | UnlockA bdg => 
          Unlock (Binding.name_of bdg)
      | SendA (bdg, term) => 
          Store (term_to_arith_expr term, Binding.name_of bdg)
      | ReceiveA (local_bdg, shared_bdg) => 
          Load (Binding.name_of local_bdg, Binding.name_of shared_bdg)
      | IfelseA ((cond_term, then_actions), else_actions) =>
          Cond (term_to_bool_expr cond_term,
                convert_actions_to_seq then_actions,
                convert_actions_to_seq else_actions)
      | WhileA (cond_term, body_actions) =>
          While (term_to_bool_expr cond_term, convert_actions_to_seq body_actions)
        
    
    and convert_actions_to_seq (actions : a_term list) : com =
      case actions of
        [] => SKIP
      | [action] => convert_action action
      | action :: rest => Seq (convert_action action, convert_actions_to_seq rest)
  in
    convert_actions_to_seq actions
  end

fun check_lock_ownership (thread_name : string) (actions : a_term list) =
  let
    fun check [] _ = NONE
      | check (LockA b :: rest) held =
          let val l = Binding.name_of b
          in
            if List.exists (fn x => x = l) held then 
              SOME ("Thread " ^ thread_name ^ ": LOCK " ^ l ^ " already held")
            else
              check rest (l :: held)
          end
      | check (UnlockA b :: rest) held =
          let val l = Binding.name_of b
          in
            if List.exists (fn x => x = l) held then
              check rest (remove (op =) l held)
            else
              SOME ("Thread " ^ thread_name ^ ": tries to UNLOCK " ^ l ^ " without holding it")
          end
      | check (_ :: rest) held = check rest held
  in
    check actions []
  end


(* Alternative CPS-style semantics *)
datatype csp_event = 
    LockEvent of string * int
  | UnlockEvent of string * int  
  | ReadEvent of string * int
  | UpdateEvent of string * int
  | AssignEvent of string * int
  | SkipEvent
(* Mise à jour de l’état fonctionnel *)
fun update_state state x v = fn y => if y = x then v else state y

(* Semantique CPS complète *)
fun sem_cps SKIP cont =
      (fn state => SkipEvent :: cont state)

  | sem_cps (Assign (x, e)) cont = 
      (fn state =>
        let
          val v = e state
        in
          AssignEvent (x, v) :: cont (update_state state x v)
        end)

  | sem_cps (Seq (P, Q)) cont = 
      sem_cps P (sem_cps Q cont)

  | sem_cps (Cond (cond, t1, t2)) cont =
      (fn state =>
        if cond state then sem_cps t1 cont state
        else sem_cps t2 cont state)

  | sem_cps (While (cond, body)) cont =
      (let
        fun loop state =
          if cond state then
            sem_cps body loop state
          else cont state
      in loop end)

  | sem_cps (Lock id) cont =
      (fn state => LockEvent (id, get_lock_id id) :: cont state)

  | sem_cps (Unlock id) cont =
      (fn state => UnlockEvent (id, get_lock_id id) :: cont state)

  | sem_cps (Store (e, x)) cont =
    (fn state =>
      let
        val v = e state
        val new_state = update_state state x v
      in
        UpdateEvent (x, v) :: cont new_state
      end)
  | sem_cps (Load (x, y)) cont =
    (fn state =>
      let
        val v = safe_lookup y state
        val new_state = update_state state x v
      in
        ReadEvent (y, v) :: cont new_state
      end)
type csp_trace = csp_event list

(* Fonction Sem adaptée avec gestion des événements CSP *)
fun sem_step (thy : theory) (cmd : com) (cont : state * csp_trace -> state * csp_trace) 
             (s : state, trace : csp_trace) : state * csp_trace =
  case cmd of
    SKIP => cont (s, trace)
  | Assign (x, expr) => 
      let 
        val new_value = expr s
        val new_state = fn v => if v = x then new_value else s v
      in 
        cont (new_state, trace) 
      end
  | Seq (p, q) => 
      sem_step thy p (fn (s', trace') => sem_step thy q cont (s', trace')) (s, trace)
  | Cond (guard, c1, c2) =>
      if guard s 
      then sem_step thy c1 cont (s, trace)
      else sem_step thy c2 cont (s, trace)
  | While (guard, body) =>
      if guard s 
      then sem_step thy body (fn (s', trace') => 
             sem_step thy (While (guard, body)) cont (s', trace')) (s, trace)
      else cont (s, trace)
  | Lock lock_name => 
      let
        val lock_id = get_lock_id lock_name
        val new_trace = LockEvent (lock_name, lock_id) :: trace
      in
        cont (s, new_trace)
      end
  | Unlock lock_name =>
      let
        val lock_id = get_lock_id lock_name
        val new_trace = UnlockEvent (lock_name, lock_id) :: trace
      in
        cont (s, new_trace)
      end
  | Store (expr, var) =>
    let
      val value = expr s
      val new_state = update_state s var value
      val new_trace = UpdateEvent (var, value) :: trace
    in
      cont (new_state, new_trace)
    end
  | Load (local_var, global_var) =>
      let
        (*TODO*)
        val read_value = s global_var
        val new_state = fn v => if v = local_var then read_value else s v
        val new_trace = ReadEvent (global_var, read_value) :: trace
      in
        cont (new_state, new_trace)
      end

(* Analyses sémantiques avancées *)

(* Détection de deadlocks simples *)
fun detect_potential_deadlock (threads : thread_absy list) : string list =
  let
    fun extract_locks_from_actions (actions : a_term list) : string list =
      let
        fun extract_from_action action =
          case action of
            LockA bdg => [Binding.name_of bdg]
          | UnlockA bdg => []
          | IfelseA ((_, then_actions), else_actions) =>
              (extract_locks_from_actions then_actions) @ 
              (extract_locks_from_actions else_actions)
          | WhileA (_, body_actions) =>
              extract_locks_from_actions body_actions
          | _ => []
      in
        List.concat (map extract_from_action actions)
      end
    
    fun get_thread_locks (thread : thread_absy) : string * string list =
      let
        val {nom_thread, actions, ...} = thread
        val locks = extract_locks_from_actions actions
      in
        (Binding.name_of nom_thread, locks)
      end
    
    val thread_locks = map get_thread_locks threads
    
    (* Détection simple : si deux threads utilisent les mêmes verrous *)
    fun find_shared_locks [] = []
      | find_shared_locks ((t1, locks1) :: rest) =
          let
            fun check_overlap (t2, locks2) =
              let
                val shared = List.filter (fn l => List.exists (fn l2 => l = l2) locks2) locks1
              in
                if null shared then NONE
                else SOME ("Potential deadlock between " ^ t1 ^ " and " ^ t2 ^ 
                          " on locks: " ^ String.concatWith ", " shared)
              end
            val warnings = List.mapPartial check_overlap rest
          in
            warnings @ find_shared_locks rest
          end
  in
    find_shared_locks thread_locks
  end

(* Détection de race conditions *)
fun detect_race_conditions (threads : thread_absy list) : string list =
  let
    fun extract_global_vars_from_actions (actions : a_term list) : (string * bool) list =
      let
        fun extract_from_action action =
          case action of
            SendA (bdg, _) => [(Binding.name_of bdg, true)]  (* write *)
          | ReceiveA (_, bdg) => [(Binding.name_of bdg, false)] (* read *)
          | IfelseA ((_, then_actions), else_actions) =>
              (extract_global_vars_from_actions then_actions) @ 
              (extract_global_vars_from_actions else_actions)
          | WhileA (_, body_actions) =>
              extract_global_vars_from_actions body_actions
          | _ => []
      in
        List.concat (map extract_from_action actions)
      end
    
    fun get_thread_global_access (thread : thread_absy) : string * (string * bool) list =
      let
        val {nom_thread, actions, ...} = thread
        val accesses = extract_global_vars_from_actions actions
      in
        (Binding.name_of nom_thread, accesses)
      end
    
    val thread_accesses = map get_thread_global_access threads
    
    (* Détection : si deux threads accèdent à la même variable et au moins un écrit *)
    fun find_races [] = []
      | find_races ((t1, accesses1) :: rest) =
          let
            fun check_race (t2, accesses2) =
              let
                fun has_conflict var =
                  let
                    val t1_writes = List.exists (fn (v, is_write) => v = var andalso is_write) accesses1
                    val t1_reads = List.exists (fn (v, is_write) => v = var andalso not is_write) accesses1
                    val t2_writes = List.exists (fn (v, is_write) => v = var andalso is_write) accesses2
                    val t2_reads = List.exists (fn (v, is_write) => v = var andalso not is_write) accesses2
                  in
                    (t1_writes orelse t1_reads) andalso (t2_writes orelse t2_reads) andalso
                    (t1_writes orelse t2_writes)
                  end
                
                val all_vars = map fst (accesses1 @ accesses2)
                val conflicting_vars = List.filter has_conflict all_vars
              in
                if null conflicting_vars then []
                else ["Potential race condition between " ^ t1 ^ " and " ^ t2 ^ 
                     " on variables: " ^ String.concatWith ", " conflicting_vars]
              end
            val warnings = List.concat (map check_race rest)
          in
            warnings @ find_races rest
          end
  in
    find_races thread_accesses
  end
(* Vérification de cohérence des types *)
fun type_check_thread (thy : theory) (thread : thread_absy) (vars_decl) : string list =
  let
    val {nom_thread, locals_decl, actions, locstab} = thread
    fun check_action_types (action, errors) =      case action of
        AssignA (bdg, term) =>
          let
            val var_name = Binding.name_of bdg
            val term_type = fastype_of term
            val expected_type_opt = 
                          case find_first (fn ((bdg', _), _) => Binding.name_of bdg' = var_name) locals_decl of
                            SOME ((_, typ), _) => SOME typ
                          | NONE => NONE
          in
            case expected_type_opt of
              SOME expected_type =>
                if term_type = expected_type then
                  errors
                else
                  ("Type mismatch in assignment to " ^ var_name ^
                   ": expected " ^ Syntax.string_of_typ_global thy expected_type ^
                   ", got " ^ Syntax.string_of_typ_global thy term_type) :: errors
            | NONE =>
                ("Variable " ^ var_name ^ " is not locally declared") :: errors
          end

      | SendA (bdg, term) =>
          let
            val var_name = Binding.name_of bdg
            val term_type = fastype_of term
            val expected_type_opt = 
                          case find_first (fn ( bdg', _, _, _) => Binding.name_of bdg' = var_name) vars_decl of
                            SOME ( _, typ, _, _) => SOME typ
                          | NONE => NONE
          in
            case expected_type_opt of
              SOME expected_type =>
                if term_type = expected_type then
                  errors
                else
                  ("Type mismatch in assignment to " ^ var_name ^
                   ": expected " ^ Syntax.string_of_typ_global thy expected_type ^
                   ", got " ^ Syntax.string_of_typ_global thy term_type) :: errors
            | NONE =>
                ("Variable " ^ var_name ^ " is not globally declared") :: errors
          end

      | ReceiveA (local_bdg, shared_bdg) =>
          let
            val local_var = Binding.name_of local_bdg
            val shared_var = Binding.name_of shared_bdg
            val local_type_opt =
                          case find_first (fn ((bdg', _), _) => Binding.name_of bdg' = local_var) locals_decl of
                            SOME ((_, typ), _) => SOME typ
                          | NONE => NONE

            val shared_type_opt =
              (* DOUBLE CHECK IF THIS CAN SAFELY BE REMOVED

              case Symtab.lookup varstab shared_var of
                SOME (SOME t) => fastype_of t
              | NONE =>
                case Symtab.lookup (!SPY |> Option.valOf |> #varstab) shared_var of
                  SOME (SOME t) => fastype_of t
                | _ => error ("Shared variable " ^ shared_var ^ " not declared")
              | SOME NONE => error ("Variable " ^ shared_var ^ " declared but has no initial value")*)
                case find_first (fn ( bdg', _, _, _) => Binding.name_of bdg' = shared_var) vars_decl of
                                            SOME ( _, typ, _, _) => SOME typ
                                          | NONE => NONE

           in
            case (local_type_opt, shared_type_opt) of
              (SOME local_type, SOME shared_type) =>
                if local_type = shared_type then 
                  errors
                else
                  ("Type mismatch in receive: cannot assign " ^ shared_var ^ " to " ^ local_var ^
                   " (expected " ^ Syntax.string_of_typ_global thy local_type ^
                   ", got " ^ Syntax.string_of_typ_global thy shared_type ^ ")") :: errors
            | (NONE, _) =>
                ("Local variable " ^ local_var ^ " not declared") :: errors
            | (_, NONE) =>
                ("Shared variable " ^ shared_var ^ " not declared") :: errors
          end
      | IfelseA ((cond, then_branch), else_branch) =>
        let
          val cond_type =
            let
              val t = cond
            in
              case cond of
                Free (x, _) =>
                  (case Symtab.lookup locstab x of
                     SOME (SOME t') => fastype_of t'
                   | SOME NONE => error ("Variable " ^ x ^ " declared but has no initial value")
                   | NONE =>
                       (case Symtab.lookup (!SPY |> Option.valOf |> #varstab) x of
                          SOME (SOME t') => fastype_of t'
                        | SOME NONE => error ("Global variable " ^ x ^ " declared but has no initial value")
                        | NONE => fastype_of t))  (* fallback to actual term type *)
              | _ => fastype_of t
            end
    
          val cond_error =
            if cond_type = @{typ bool} then []
            else ["Condition must be boolean, got: " ^ Syntax.string_of_typ_global thy cond_type]
    
          val then_errors = List.foldl check_action_types [] then_branch
          val else_errors = List.foldl check_action_types [] else_branch
        in
          cond_error @ then_errors @ else_errors @ errors
        end

     | WhileA (cond, body) =>
            let
              val cond_type =
                let
                  val t = cond
                in
                  case cond of
                    Free (x, _) =>
                      (case Symtab.lookup locstab x of
                         SOME (SOME t') => fastype_of t'
                       | SOME NONE => error ("Variable " ^ x ^ " declared but has no initial value")
                       | NONE =>
                           (case Symtab.lookup (!SPY |> Option.valOf |> #varstab) x of
                              SOME (SOME t') => fastype_of t'
                            | SOME NONE => error ("Global variable " ^ x ^ " declared but has no initial value")
                            | NONE => fastype_of t))  (* fallback *)
                  | _ => fastype_of t
                end
        
              val cond_error =
                if cond_type = @{typ bool} then []
                else ["While condition must be boolean, got: " ^ Syntax.string_of_typ_global thy cond_type]
        
              val body_errors = List.foldl check_action_types [] body
            in
              cond_error @ body_errors @ errors
            end

      | _ => errors

  in
    List.foldl check_action_types [] actions
  end

fun build_initial_state_for_thread 
      (globals : (binding * typ * Position.T * term option) list) 
      (locals : ((binding * typ) * term option) list) (thy: theory) : state =
  let
    fun term_to_int t_opt =
        case t_opt of
            NONE => 0
          | SOME t => eval_term_to_int thy t (fn _ => 0)

    val global_vals = map (fn (bdg, _, _, t_opt) =>
                            (Binding.name_of bdg, term_to_int t_opt)) globals

    val local_vals  = map (fn ((bdg, _), t_opt) =>
                            (Binding.name_of bdg, term_to_int t_opt)) locals

    val all_vals = local_vals @ global_vals
  in
    fn var => case AList.lookup (op =) all_vals var of
                SOME v => v
              | NONE => 0
  end

(* Fonction de vérification sémantique principale complète *)
fun semantic_check (absy_data : absy) (thy : theory) : theory =
  let
    val {system, globals_decls, varstab, locks_decls, threads_decls} = absy_data
    
    val _ = message false ("=== SEMANTIC ANALYSIS FOR SYSTEM: " ^ 
                          Binding.name_of system ^ " ===")
    
    (* Vérification 1: Analyse des deadlocks *)
    val deadlock_warnings = detect_potential_deadlock threads_decls
    val _ = if null deadlock_warnings then 
              message false "✓ No potential deadlocks detected"
            else 
              (message false "DEADLOCK WARNINGS:";
               map (message false) deadlock_warnings; ())
    
    (* Vérification 2: Analyse des race conditions *)
    val race_warnings = detect_race_conditions threads_decls  
    val _ = if null race_warnings then
              message false "✓ No race conditions detected"
            else
              (message false "RACE CONDITION WARNINGS:";
               map (message false) race_warnings; ())
    
    (* Vérification 3: Vérification des types pour chaque thread *)
    fun check_thread globals_decls (thread : thread_absy) : unit =
      let
        val {nom_thread, locals_decl, actions, locstab} = thread
        val thread_name = Binding.name_of nom_thread
        
        val _ = message false ("Analyzing thread: " ^ thread_name)
        
        (* Conversion vers com pour analyse sémantique *)
        val com_program = convert_to_com thy actions varstab locstab

        val initial_state = build_initial_state_for_thread globals_decls locals_decl thy
        val cps_trace = sem_cps com_program (fn _ => []) initial_state

        val _ = message false (" ✓ CPS-style trace for " ^ thread_name ^ ":")
        val _ = List.app (fn ev => message false ("    " ^ @{make_string} ev)) cps_trace
        (* Vérification des types *)
        val type_errors = type_check_thread thy thread globals_decls
        val _ = if null type_errors then
                  message false (" ✓ Type checking passed for " ^ thread_name)
                else
                  (message false (" ✗ Type errors in " ^ thread_name ^ ":");
                   map (fn err => message false ("    " ^ err)) type_errors; ())
        (* Vérification que lock et unlock respectent des regles d'appartenance *)
        val _ = case check_lock_ownership thread_name actions of
          NONE => ()
        | SOME msg => error msg

        (* Simulation d'exécution pour détecter d'autres problèmes *)
        val initial_state = build_initial_state_for_thread globals_decls locals_decl thy
        val (final_state, execution_trace) = 
          sem_step thy com_program (fn (s, t) => (s, t)) (initial_state, [])
        
        val _ = message false ("  ✓ Execution simulation completed for " ^ thread_name)
        val _ = message false (" Generated " ^ 
                             Int.toString (length execution_trace) ^ " CSP events")
      in
        ()
      end
    
    val _ = map (check_thread globals_decls) (threads_decls)
    
    (* Vérification 4: Cohérence globale du système *)
    val _ = message false "=== GLOBAL SYSTEM CONSISTENCY ==="
    
    (* Vérifier que tous les verrous utilisés sont déclarés *)
    fun check_lock_declarations () =
      let
        val declared_locks = map (fn (bdg, _, _) => Binding.name_of bdg) locks_decls
        
        fun extract_used_locks_from_thread (thread : thread_absy) =
          let
            fun extract_from_actions actions =
              List.concat (map (fn action =>
                case action of
                  LockA bdg => [Binding.name_of bdg]
                | UnlockA bdg => [Binding.name_of bdg]
                | IfelseA ((_, then_acts), else_acts) =>
                    extract_from_actions then_acts @ extract_from_actions else_acts
                | WhileA (_, body_acts) => extract_from_actions body_acts
                | _ => []) actions)
          in
            extract_from_actions (#actions thread)
          end
        
        val used_locks = List.concat (map extract_used_locks_from_thread threads_decls)
        val undeclared_locks = List.filter (fn used => 
          not (List.exists (fn decl => decl = used) declared_locks)) used_locks
      in
        if null undeclared_locks then
          message false "✓ All used locks are properly declared"
        else
          (message false "✗ Undeclared locks used:";
           map (fn lock => message false ("  " ^ lock)) undeclared_locks; ())
      end
    
    val _ = check_lock_declarations ()
    
    (* Vérifier que toutes les variables globales utilisées sont déclarées *)
    fun check_global_var_declarations () =
      let
        val declared_globals = map (fn (bdg, _, _, _) => Binding.name_of bdg) globals_decls
        
        fun extract_used_globals_from_thread (thread : thread_absy) =
          let
            fun extract_from_actions actions =
              List.concat (map (fn action =>
                case action of
                  SendA (bdg, _) => [Binding.name_of bdg]
                | ReceiveA (_, bdg) => [Binding.name_of bdg]
                | IfelseA ((_, then_acts), else_acts) =>
                    extract_from_actions then_acts @ extract_from_actions else_acts
                | WhileA (_, body_acts) => extract_from_actions body_acts
                | _ => []) actions)
          in
            extract_from_actions (#actions thread)
          end
        
        val used_globals = List.concat (map extract_used_globals_from_thread threads_decls)
        val undeclared_globals = List.filter (fn used => 
          not (List.exists (fn decl => decl = used) declared_globals)) used_globals
      in
        if null undeclared_globals then
          message false "✓ All used global variables are properly declared"
        else
          (message false "✗ Undeclared global variables used:";
           map (fn var => message false ("  " ^ var)) undeclared_globals; ())
      end
    
    val _ = check_global_var_declarations ()
    
    val _ = message false "=== SEMANTIC CHECK COMPLETED ==="
  in
    thy
  end

fun semantics (absy_cl: theory -> absy) (thy : theory) = 
  let
    val absy_data = absy_cl thy
  in
    semantic_check absy_data thy
  end

fun sequence_actions [] = SkipA
  | sequence_actions [a] = a
  | sequence_actions (a::rest) = SeqA (a, sequence_actions rest)

(*Fonction pour générer le code CSP complet *)
fun generate_csp_code (absy_data : absy) (thy : theory) : string =
let
    val {system, globals_decls, locks_decls, threads_decls, varstab} = absy_data
    val system_name = Binding.name_of system

    (*Génération des événements CSP *)
    fun generate_events () =
      let
        val lock_events = map (fn (bdg, _, _) => 
          let val name = Binding.name_of bdg
          in "channel lock_" ^ name ^ ", unlock_" ^ name ^ " : Int"
          end) locks_decls

        val global_events = map (fn (bdg, _, _, _) =>
          let val name = Binding.name_of bdg  
          in "channel read_" ^ name ^ ", update_" ^ name ^ " : Int"
          end) globals_decls
      in
        String.concatWith "\n" (lock_events @ global_events)
      end

    (*Conversion d'une action en CSP *)
fun action_list_to_csp [] state thy = ("SKIP", state)
  | action_list_to_csp [a] state thy = action_to_csp a state thy
  | action_list_to_csp (a::rest) state thy =
      let
        val (s1, state1) = action_to_csp a state thy
        val (s2, state2) = action_list_to_csp rest state1 thy
      in
        if (a =SkipA) then 
          (s2, state2)
        else
          (s1 ^ "→" ^ s2, state2)
      end

and action_to_csp action state thy =
  case action of
   SkipA => ("SKIP", state)
  | LockA bdg => ("lock_" ^ Binding.name_of bdg ^ "!0", state)
  | UnlockA bdg => ("unlock_" ^ Binding.name_of bdg ^ "!0", state)
  | AssignA (bdg, term) =>
      let
        val name = Binding.name_of bdg
        val typ = fastype_of term
        val v = if typ = @{typ bool}
                then if eval_term_to_bool thy term state then 1 else 0
                else eval_term_to_int thy term state
        val new_state = update_state state name v
      in
        ("update_" ^ name ^ "!" ^ Int.toString v, new_state)
      end
  | SendA (bdg, term) =>
      let
        val name = Binding.name_of bdg
        val typ = fastype_of term
        val v = if typ = @{typ bool}
                then if eval_term_to_bool thy term state then 1 else 0
                else eval_term_to_int thy term state
        val new_state = update_state state name v
      in
        ("update_" ^ name ^ "!" ^ Int.toString v, new_state)
      end
  | ReceiveA (local_bdg, global_bdg) =>
      let
        val global_var_name = Binding.name_of global_bdg
        val v = safe_lookup global_var_name state
        val local_var_name = Binding.name_of local_bdg
        val new_state = update_state state local_var_name v
      in
        ("read_" ^ global_var_name ^ "!" ^ Int.toString v, new_state)
      end
  | IfelseA ((cond, a1), a2) =>
      let
        val b = eval_term_to_bool thy cond state
        val val_str = if b then "true" else "false"
        val (then_code, _) = action_list_to_csp a1 state thy
        val (else_code, _) = action_list_to_csp a2 state thy
      in
        ("{ (" ^ val_str ^ " & " ^ then_code ^ ") [] (¬" ^ val_str ^ " & " ^ else_code ^ ") }", state)
      end
  | WhileA (cond, body) =>
      let
        val val_str = if eval_term_to_bool thy cond state then "true" else "false"
        val (body_code, _) = action_list_to_csp body state thy
      in
        ("{ (" ^ val_str ^ " &  µ X." ^ body_code ^ " -> X) [] (¬" ^ val_str ^" & (SKIP) ) }", state)
      end


    (* Conversion d’un thread vers CSP *)
        fun thread_to_csp globals_decls (thread : thread_absy) thy : string =
          let
            val {nom_thread, actions, locals_decl, ...} = thread
            val thread_name = Binding.name_of nom_thread
        
            val initial_state = build_initial_state_for_thread globals_decls locals_decl thy
            val (code, _) = action_list_to_csp actions initial_state thy
          in
            thread_name ^ " = " ^ code 
          end
          
    fun generate_threads globals_decls threads_decls thy =
        String.concatWith "\n" (map (fn t => thread_to_csp globals_decls t thy) threads_decls)

    (*Génération du système global *)
    fun generate_system () =
      let
        val thread_names = map (fn t => Binding.name_of (#nom_thread t)) threads_decls
      in
        system_name ^ " = " ^ String.concatWith " ||| " thread_names
      end

  in
    String.concatWith "\n\n" [
      "-- Channels",
      generate_events (),
      "",
      "-- Threads",
      generate_threads globals_decls threads_decls thy,
      "",
      "-- System",
      generate_system ()
    ]
  end


›

section‹Semantic Encoding›
(**************************En travaux***********************)
(*definition SKIP_process :: "(sema_evs + glo_vars_ev) process"
  where "SKIP_process ≡ Skip"
ML‹

  (* Convertir une liste de a_term en une seule commande de type com *)
fun sequence_actions [] = SkipA
  | sequence_actions [a] = a
  | sequence_actions (a :: rest) = SeqA (a, sequence_actions rest)

(* Conversion d’une action abstraite (a_term) vers le terme logique com *)
fun quote_com SkipA =
      @{term "SKIP :: com"}  
    | quote_com (AssignA (b, e)) =
      let
        val var_str = HOLogic.mk_string (Binding.name_of b)
      in
        @{term assign} $ var_str $ e
      end
  | quote_com (SeqA (c1, c2)) =
      @{term seq} $ quote_com c1 $ quote_com c2
  | quote_com (LockA b) =
      let val n = HOLogic.mk_number @{typ int} (Int.fromString (Binding.name_of b) |> the)
      in @{term lock} $ n end
  | quote_com (UnlockA b) =
      let val n = HOLogic.mk_number @{typ int} (Int.fromString (Binding.name_of b) |> the)
      in @{term unlock} $ n end
  | quote_com (SendA (sv, e)) =
      let val sv_str = HOLogic.mk_string (Binding.name_of sv)
      in @{term send} $ e $ sv_str end
  | quote_com (ReceiveA (v, sv)) =
      let
        val v_str = HOLogic.mk_string (Binding.name_of v)
        val sv_str = HOLogic.mk_string (Binding.name_of sv)
      in
        @{term rec} $ v_str $ sv_str
      end
  | quote_com (IfelseA ((cond, then_branch), else_branch)) =
      @{term cond} $ cond
                  $ quote_com (sequence_actions then_branch)
                  $ quote_com (sequence_actions else_branch)
  | quote_com (WhileA (cond, body)) =
      @{term while} $ cond
                    $ quote_com (sequence_actions body)

›*)
section‹Semantic Encoding›

definition SKIP_process :: "(sema_evs + glo_vars_ev) process"
  where "SKIP_process ≡ Skip"

ML‹
(* Convertir une liste de a_term en une seule commande de type com *)
fun sequence_actions [] = SkipA
  | sequence_actions [a] = a
  | sequence_actions (a :: rest) = SeqA (a, sequence_actions rest)

(* Conversion d'une action abstraite (a_term) vers le terme logique com *)
fun quote_com SkipA =
      @{term "SKIP :: com"}  
  | quote_com (AssignA (b, e)) =
      let
        val var_str = HOLogic.mk_string (Binding.name_of b)
      in
        @{term assign} $ var_str $ e
      end
  | quote_com (SeqA (c1, c2)) =
      @{term seq} $ quote_com c1 $ quote_com c2
  | quote_com (LockA b) =
      let 
        val n_str = Binding.name_of b
        val n = case Int.fromString n_str of
                  SOME i => HOLogic.mk_number @{typ nat} i
                | NONE => error ("Invalid lock number: " ^ n_str)
      in 
        @{term "com.lock :: int ⇒ com"} $ n 
      end
  | quote_com (UnlockA b) =
      let 
        val n_str = Binding.name_of b
        val n = case Int.fromString n_str of
                  SOME i => HOLogic.mk_number @{typ nat} i
                | NONE => error ("Invalid unlock number: " ^ n_str)
      in 
        @{term "com.unlock :: int ⇒ com"} $ n 
      end
  | quote_com (SendA (sv, e)) =
      let val sv_str = HOLogic.mk_string (Binding.name_of sv)
      in @{term "send :: (σ ⇒ nat) ⇒ string ⇒ com"} $ e $ sv_str end
  | quote_com (ReceiveA (v, sv)) =
      let
        val v_str = HOLogic.mk_string (Binding.name_of v)
        val sv_str = HOLogic.mk_string (Binding.name_of sv)
      in
        @{term "rec :: string ⇒ string ⇒ com"} $ v_str $ sv_str
      end
  | quote_com (IfelseA ((cond, then_branch), else_branch)) =
      @{term cond} $ cond
                  $ quote_com (sequence_actions then_branch)
                  $ quote_com (sequence_actions else_branch)
  | quote_com (WhileA (cond, body)) =
      @{term while} $ cond
                    $ quote_com (sequence_actions body)
›

ML‹
(* Fonction pour déclarer les termes des threads *)
fun declare_thread_terms (thy: theory) (threads: thread_absy list)
                         (varstab: (term option) Symtab.table)
                         : theory =
  fold (fn {nom_thread, actions, locstab, ...} => fn thy' =>
    let
      val name = Binding.name_of nom_thread
      val bname = Binding.name (name ^ "_term")

      (* Convert actions into com *)
      val com_ast = sequence_actions actions
      val com_term = quote_com com_ast

      (* Create a simple definition: thread_name_term = com_term *)
      val lthy = Named_Target.theory_init thy'
      val ((_, term_def), lthy') =
        Local_Theory.define ((bname, NoSyn), ((Binding.empty, []), com_term)) lthy
      val thy'' = Local_Theory.exit_global lthy'
      
      val _ = writeln ("✓ Defined command term: " ^ Binding.name_of bname)

      (* Optionally, create the semantic term separately *)
      val sem_bname = Binding.name (name ^ "_sem")
      val cont = Abs ("s", @{typ σ}, @{term "SKIP_process"})
      val sem_term = @{const Sem⇩0} $ com_term $ cont
      
      val lthy2 = Named_Target.theory_init thy''
      val ((_, sem_def), lthy2') =
        Local_Theory.define ((sem_bname, NoSyn), ((Binding.empty, []), sem_term)) lthy2
      val thy''' = Local_Theory.exit_global lthy2'
      
      val _ = writeln ("✓ Defined semantic term: " ^ Binding.name_of sem_bname)

    in
      thy'''
    end)
    threads thy
›

ML‹
(* Fonction pour générer les termes sémantiques *)
fun generate_terms (absy_data : absy) (thy : theory) : theory =
  let 
    val {system, globals_decls, locks_decls, threads_decls, varstab} = absy_data
    val system_name = Binding.name_of system

    (* Fonction pour vérifier l'égalité des termes dans une table *)
    fun term_equals_in_table (tab : (term option) Symtab.table) (b : binding) (t : term) : bool =
      case Symtab.lookup tab (Binding.name_of b) of
        SOME (SOME t') => Term.aconv (t, t')
      | _ => false

    (* Fonction pour mettre à jour l'état *)
    fun update_state (locstab : (term option) Symtab.table)
                     (globtab : (term option) Symtab.table)
                     (state : term -> int)
                     (x : binding)
                     (v : int) : term -> int =
      let
        val x_name = Binding.name_of x
        fun equals_var y =
          case Symtab.lookup locstab x_name of
            SOME (SOME t') => Term.aconv (y, t')
          | _ =>
              (case Symtab.lookup globtab x_name of
                 SOME (SOME t'') => Term.aconv (y, t'')
               | _ => false)
      in
        fn y => if equals_var y then v else state y
      end

    (* Fonction d'évaluation basique d'un terme *)
    fun eval_term (t : term) (state : term -> int) : int =
      case t of
        Const (@{const_name "Groups.zero_class.zero"}, _) => 0
      | Const (@{const_name "Groups.one_class.one"}, _) => 1
      | _ => 0  (* Évaluation simplifiée, à étendre selon les besoins *)

    (* Fonction pour convertir une action en terme *)
    fun action_to_term (action : a_term)
                       (state : term -> int)
                       (locstab : term option Symtab.table)
                       (globtab : term option Symtab.table)
        : term * (term -> int) =
      case action of
        SkipA => 
          (@{term "SKIP :: com"}, state)
          
      | AssignA (name, assignation) =>
          let
            val v = eval_term assignation state
            val updated_state = update_state locstab globtab state name v
            val name_str = HOLogic.mk_string (Binding.name_of name)
            val assign_term = @{term assign} $ name_str $ assignation
          in
            (assign_term, updated_state)
          end

      | SeqA (SkipA, C) =>
          action_to_term C state locstab globtab

      | SeqA (A, B) =>
          let
            val (term_A, stateA) = action_to_term A state locstab globtab
            val (term_B, stateB) = action_to_term B stateA locstab globtab
            val seq_term = @{term seq} $ term_A $ term_B
          in
            (seq_term, stateB)
          end

      | LockA name =>
          let
            val n_str = Binding.name_of name
            val n = case Int.fromString n_str of
                      SOME i => HOLogic.mk_number @{typ nat} i
                    | NONE => error ("Invalid lock number: " ^ n_str)
            val lock_term = @{term lock} $ n
          in
            (lock_term, state)
          end

      | UnlockA name =>
          let
            val n_str = Binding.name_of name
            val n = HOLogic.mk_number @{typ nat} (get_lock_id n_str)
            (*val n = case Int.fromString n_str of
                      SOME i => HOLogic.mk_number @{typ nat} i
                    | NONE => error ("Invalid unlock number: " ^ n_str)*)
            val unlock_term = @{term unlock} $ n
          in
            (unlock_term, state)
          end

      | _ => 
          error ("Unsupported action type in action_to_term")

    (* État par défaut *)
    fun default_state (_ : term) = 0

    (* Traiter tous les threads *)
    val _ = List.app (fn {nom_thread, actions, locstab, ...} =>
      case actions of
        [] => writeln ("Thread " ^ Binding.name_of nom_thread ^ " has no actions")
      | _ =>
          let
            val _ = writeln ("== Processing thread " ^ Binding.name_of nom_thread ^ " ==")
            val com_ast = sequence_actions actions
            val (res_term, final_state) = action_to_term com_ast default_state locstab varstab
            val _ = writeln ("✓ Successfully processed thread " ^ Binding.name_of nom_thread)
          in
            ()
          end
    ) threads_decls

    (* Déclarer les termes des threads dans la théorie *)
    val thy' = declare_thread_terms thy threads_decls varstab
  in
    thy'
  end
›

(**********************************************************)


section‹Impression›
ML‹
val _ =
  Outer_Syntax.command \<^command_keyword>‹SYSTEM› "defines System Specification"
    (parse_system_spec >>
     (fn system_data => Toplevel.theory (fn thy =>
      let
        val checked = context_check system_data thy
        val thy_sem = semantic_check checked thy
        val lthy = Named_Target.theory_init thy_sem

        (* Générer et afficher les termes sémantiques *)
        fun process_thread ({nom_thread, actions, locstab, ...}: thread_absy) =
          let
            val name = Binding.name_of nom_thread
            val com_ast = sequence_actions actions
            val com_term = quote_com com_ast
            val cont = Abs ("s", @{typ σ}, @{term "SKIP_process"})
            val sem_term = @{const Sem⇩0} $ com_term $ cont
            
            val _ = writeln ("=== Thread: " ^ name ^ " ===")
            val _ = writeln ("Command term:")
            val _ = writeln ("  " ^ Syntax.string_of_term_global thy_sem com_term)
            val _ = writeln ("Semantic term:")  
            val _ = writeln ("  " ^ Syntax.string_of_term_global thy_sem sem_term)
            val _ = writeln ("Suggested definition:")
            val _ = writeln ("definition " ^ name ^ "_cmd :: com where")
            val _ = writeln ("  \"" ^ name ^ "_cmd = " ^ Syntax.string_of_term_global thy_sem com_term ^ "\"")
            val _ = writeln ("definition " ^ name ^ "_sem :: \"σ ⇒ (sema_evs + glo_vars_ev) process\" where")
            val _ = writeln ("  \"" ^ name ^ "_sem = " ^ Syntax.string_of_term_global thy_sem sem_term ^ "\"")
            val _ = writeln ""
          in
            ()
          end

        val _ = writeln "=== SEMANTIC TERMS GENERATION ==="
        val _ = List.app process_thread (#threads_decls checked)

        val thy' = Local_Theory.exit_global lthy

       (* val _ = Output.writeln "=== CSP CODE GENERATION ==="
        val csp_code = generate_csp_code checked thy'
        val _ = Output.writeln ("Generated CSP: " ^ csp_code)
*)
      in thy' end)))

›



section‹Tests›

SYSTEM S
  globals v :nat= ‹4::nat› x :bool = True val_test : nat = ‹5::nat›
  locks   l: nat
  thread t :
       any var_local:‹nat›
       actions 
        SKIP; 
        LOCK 4;
        v->‹val_test›;
  thread m:
       any var_local :int = ‹4 :: int›  test : int = ‹-3 ::int›
       actions SKIP;
       var_local = ‹(4+42) :: int›;
      test = ‹2* var_local :: int›;
      test = ‹test+3 :: int›;
      IF ‹x› THEN 
                  WHILE ‹x› DO 
                    test = ‹test-3 :: int›;
                  DONE 
               ELSE
                        test = ‹test+3 :: int›;
               DONE
end;


SYSTEM WellTypedSys
  globals v:‹bool› = ‹True› x:‹bool› = False var1:‹int› 
  locks   l:‹()›                                       
  thread t1 : 
         any y : ‹int› = ‹36 :: int›
         actions 
         SKIP;
         LOCK l;
         v ->‹False›;                                             
         UNLOCK l;
         IF ‹x› THEN 
            WHILE x DO 
              LOCK l; 
              UNLOCK l;                                                         
            DONE 
         ELSE
            SKIP;
         DONE
        y  = ‹y+2 :: int›;
        y  = ‹y+2 :: int›;
        var1 -> ‹y :: int›;

thread t2 :
         any var2:‹nat› = ‹(4+6) :: nat› y : ‹nat› = ‹28 :: nat›
         actions 
         SKIP;
         LOCK l;
         v ->‹3=2›;
         v ->‹True›;
         v ->‹False›;
         UNLOCK l;
         IF ‹v› THEN 
            WHILE ‹v› DO 
              LOCK l; 
              UNLOCK l;
            DONE 
         ELSE
            SKIP;
         DONE
        y = ‹var2 + 3 :: nat›; 

end;


ML‹



fun replace_all _ _ "" = ""
  | replace_all target replacement input =
      if String.isPrefix target input
      then replacement ^ replace_all target replacement (String.extract (input, String.size target, NONE))
      else String.str (String.sub (input, 0)) ^ replace_all target replacement (String.extract (input, 1, NONE))

fun escape_latex_string s =
  s
  (*|> replace_all "\\" "\\textbackslash{}"*)
  |> replace_all "_" "\\_"
  |> replace_all "%" "\\%"
  |> replace_all "&" "\\&"
  |> replace_all "{" "\\{"
  |> replace_all "}" "\\}"
  |> replace_all "^" "\\^{} "
  |> replace_all "~" "\\~{} "
  |> replace_all "¬" " \\neg "
  |> replace_all "µ" " \\mu "
  |> replace_all "→" " \\rightarrow "


val trim = Library.trim_line







fun visualize_csp_threads_simple (absy: absy) (thy: theory) : string =
  let
    val      {system          : binding,
             globals_decls   : (binding * typ * Position.T * term option) list,
             varstab         : (term option) Symtab.table,
             locks_decls     : (binding * term * Position.T) list,
             threads_decls   : thread_absy list
            }
            = absy 
    val sys_name = Binding.name_of system
    val full_csp = generate_csp_code absy thy
    val lines = String.tokens (fn c => c = #"\n") full_csp
 open Latex
    fun is_thread_definition line =
      String.isSubstring " = " line andalso
      not (String.isSubstring "channel" line) andalso
      not (String.isSubstring "-- " line) andalso
      not (String.isSubstring " ||| " line) andalso
      line <> ""

    fun to_box line =
      case String.tokens (fn c => c = #"=") line of
        [lhs, rhs] =>
          let
            val name = trim lhs
            val body = trim rhs
            val escaped_name = escape_latex_string name
            val escaped_body = escape_latex_string (name ^ " = " ^ body)
          in
            "\\fbox{\\begin{minipage}[t]{0.9\\textwidth}\n" ^
            "\\centering\n" ^
            "\\textbf{" ^ escaped_name ^ "} \\\\\n" ^
            "\\texttt{" ^ escape_latex_string body ^ "}\n" ^
            "\\end{minipage}}"
          end
      | _ => "% skipped malformed line"

    val thread_boxes =
      lines |> List.filter is_thread_definition |> map to_box 

    fun show_global (bdg, T, _, init_opt) =
      let
        val name     = Binding.name_of bdg
        val typ_str  = Syntax.string_of_typ_global thy T
        val init_str =
          (case init_opt of
             NONE   => ""
           | SOME t => " = " ^ Syntax.string_of_term_global thy t)  
      in
        "\\texttt{" ^
        escape_latex_string (name ^ " : "  ^ init_str) ^
        "}\\\\"
      end

    val globals_block =
      if null globals_decls
      then "\\texttt{(no globals)}"
      else String.concatWith "\n" (map show_global globals_decls)


    val pre_code =
      "\\fbox{\\begin{minipage}[t]{0.9\\textwidth}\n" ^
      "\\centering\n" ^
      "\\textbf{System " ^ escape_latex_string sys_name ^ "}\\\\[4pt]\n" ^
      globals_block ^ "\n" ^
      "\\end{minipage}}"

  in
    String.concatWith "\n\n" (pre_code :: thread_boxes) 
 end

val _ =
  Theory.setup
    (Document_Output.antiquotation_raw \<^binding>‹show_csp›
      (Scan.succeed ())
      (fn ctxt => fn () =>
        case !SPY of
           SOME absy =>  
             let
               val thy = Proof_Context.theory_of ctxt
               val csp_display = visualize_csp_threads_simple absy thy
             in
                  Latex.string csp_display
             end
        | NONE => Latex.string "\\textit{No parsed system available.}"))
›
(*>*)
text ‹
  This is the AST of the last SYSTEM: \\
   @{show_csp}
›




(*<*)end  (*>*)
