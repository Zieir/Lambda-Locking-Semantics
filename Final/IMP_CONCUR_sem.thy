theory IMP_CONCUR_sem

    imports (* "../afp-2025-05-05/thys/*) "HOL-CSPM.CSPM" Main

begin
ML_file "../hol-csp2.0/FDR4/CSPM-API.ML"

section‹Introduction›

text‹
‹IMP⇩c⇩o⇩n⇩c⇩u⇩r› is intended to provide a more common (though still theoretic)
programming-language aspect to CSP, and could be an interesting object
of study in itself. An interesting question is, for example,
how  a Hoare Calculus for ‹IMP⇩c⇩o⇩n⇩c⇩u⇩r› would look like, or how a conversion
to FDR4 could be used in a SPIN-like manner as verification backend 
for practical purposes.

‹IMP⇩c⇩o⇩n⇩c⇩u⇩r› comprises the standard elements of the IMP - language (‹SKIP›, ‹assignment›,
‹IF _ THEN _ ELSE›, ‹WHILE _ DO _› and the sequential composition ‹_ ; _›), plus 
the new features:
   ▸ semaphores with ‹lock› and ‹unlock›, and
   ▸ thread-global shared variables accessible 
     via ‹LOAD› and ‹STORE› operations.

This file contains:
   ▸ the abstract and concrete syntax of ‹IMP⇩c⇩o⇩n⇩c⇩u⇩r›
   ▸ bricks-specifications for semaphores and global shared variables,
   ▸ a denotational semantics of ‹IMP⇩c⇩o⇩n⇩c⇩u⇩r› converting ‹IMP⇩c⇩o⇩n⇩c⇩u⇩r›-program 
     systems into HOL-CSPM, and
   ▸ some examples and tests.

The general theory should be developed elsewhere; this sample file shows the 
global construction principle of a combined semantics.›

section‹Technical Prelimiaries›
text‹TO BE REMOVED WHEN BASED ON MORE MODERN HOL-CSP VERSIONS."›
lemma cont_fun_iff:
  ‹cont f ⟷ (∀z. cont (λx. f x z))›
  by (metis cont2cont_fun cont2cont_lambda)

simproc_setup apply_cont (‹cont (λf. E f)›) = ‹
  K (fn ctxt => fn ct =>
     let val t = Thm.term_of ct
         val foo = case t of _ $ foo => foo
     in  case foo of Abs (_, _, expr) =>
              if   fst (strip_comb expr) = Bound 0
              (* since ‹λf. E f› is too permissive, we ensure that the term is of the
                 form ‹λf. f ...› (for example ‹λf. f x›, or ‹λf. f x y›, etc.) *)
              then let val tac = Metis_Tactic.metis_tac ["no_types"] "combs" ctxt
                                 @{thms cont_fun_iff cont_id}
                       val rwrt_ct  = HOLogic.mk_judgment (Thm.apply \<^cterm>‹λlhs. lhs = True› ct)
                       val rwrt_thm = Goal.prove_internal ctxt [] rwrt_ct (fn _ => tac 1)
                   in  SOME (mk_meta_eq rwrt_thm)
                   end
              else NONE
            | _ => NONE
     end
    )
›

section‹The Syntax of ‹IMP⇩c⇩o⇩n⇩c⇩u⇩r››

type_synonym SV = string  ― ‹Shared Variables›
type_synonym V  = string  ― ‹(Thread-)Local Variables›
type_synonym MV = int     ― ‹Mutual exclusion variables (MUTEX ids)›

type_synonym D = int

type_synonym "σ" = ‹V ⇒ D›

type_synonym "E⇩a⇩r⇩i⇩t⇩h" = ‹σ ⇒ D›
type_synonym "E⇩b⇩o⇩o⇩l"  = ‹σ ⇒ bool›


datatype com = SKIP
             | assign  V E⇩a⇩r⇩i⇩t⇩h       (" _ := _" [90,90]80)
             | seq     com com       (infixl ";" 78)
             | cond   "E⇩b⇩o⇩o⇩l" com com ("IF (_)/ THEN (_)/ ELSE (_)/" 
                                               [0,0,79]79)
             | while  "E⇩b⇩o⇩o⇩l" com     ("WHILE (_)/ DO (_)" [0,80]80)

             | lock    MV
             | unlock  MV            
             | send    E⇩a⇩r⇩i⇩t⇩h SV      ("STORE _ TO  _" [90,90]80)              
             | rec     V SV          ("LOAD _ FROM _" [90,90]80)


text‹Two example threads:›

definition Thread1 where
      ‹ Thread1 ≡ SKIP
      ›

definition Thread2 where
      ‹ Thread2 ≡ SKIP ; 
                  ''a'' :=  (λσ. 1 + 2); 
                  IF (λσ. σ ''d'' > 3) THEN lock 4 ELSE lock 3;  
                  WHILE (λσ. True) DO lock 4 ;  
                  STORE (λσ. σ ''d'' + 1) TO ''b''; 
                  LOAD ''a'' FROM  ''b''; 
                  unlock 3
      ›
definition m_cmd where 
  "m_cmd = SKIP ;
           ( ''var_local'' := (λσ. 4 + 42) ;
            ( ''test'' := (λσ. 2 * σ ''var_local'') ;
             ( ''test'' := (λσ. σ ''test'' + 3) ;
              IF (λσ. σ ''x''>5)
              THEN WHILE (λσ. σ ''x'' >5) DO  ''test'' := (λσ. σ ''test'' - 3)
              ELSE  ''test'' := (λσ. σ ''test'' + 3))))"
ML‹
val x = \<^term>‹Thread2›
›
section‹Preliminaries: Simulating Bricks.›
subsection‹A simplistic model of a semaphore family›
(* (this should be a locale) *)
(*datatype   sema_evs = lock int | unlock int *)


datatype evs = lock int | unlock int | read_glo ‹SV› ‹D› | update_glo ‹SV› ‹D› | read_loc ‹SV› ‹D› | update_loc ‹SV› ‹D› 


definition semaphore :: "int ⇒ evs process"
    where "semaphore ≡ μ X. (λn. lock n → unlock n → X n) "

lemma sema_rec : "semaphore n = lock n → unlock n → semaphore n"
  by (subst cont_process_rec[OF semaphore_def[THEN meta_eq_to_obj_eq]]) simp_all

subsection‹A simplistic model of a thread-global variable family›
(* (this should be a locale) *)


(*datatype   vars_ev = read_glo ‹SV› ‹D› | update_glo ‹SV› ‹D› | read_loc ‹SV› ‹D› | update_loc ‹SV› ‹D›*)

definition global_vars :: "σ ⇒ SV ⇒ evs process" 
  where   ‹global_vars ≡ μ X.   (λ σ. (λ id.  ((read_glo id)❙!(σ id) → X σ id ) 
                                            □ ((update_glo id)❙?v → X (σ(id := v)) id )))›


lemma global_vars_rec : "global_vars σ n =    ((read_glo n)❙!(σ n) → global_vars σ n) 
                                           □ ((update_glo n)❙?v → global_vars (σ(n := v)) n)" 
  by (subst cont_process_rec[OF global_vars_def[THEN meta_eq_to_obj_eq]]) simp_all



(*Modifs*)

definition locals_vars :: " σ ⇒ SV ⇒evs process" 
  where   ‹locals_vars ≡ μ X.   (λ σ. (λ id.  ((read_loc id)❙!(σ id) → X σ id) 
                                            □ ((update_loc id)❙?v → X (σ(id := v)) id )))›




section‹Denotational Semantics of ‹IMP⇩c⇩o⇩n⇩c⇩u⇩r››

fun Sem⇩0 :: "com ⇒ (σ ⇒ evs  process) ⇒ σ ⇒ evs process" 
  where "Sem⇩0 SKIP C                   = C" 
       |"Sem⇩0 (x := E) C               = (λ σ. C (σ(x := E σ)))"
       |"Sem⇩0 (P ; Q) C                = Sem⇩0 P (Sem⇩0 Q C)" 
       |"Sem⇩0 (IF E THEN C1 ELSE C2) C = (λ σ. if E σ then Sem⇩0 C1 C σ else Sem⇩0 C2 C σ)"
       |"Sem⇩0 (WHILE E DO B) C         = (μ X. (λ σ. if E σ then Sem⇩0 B X σ else C σ))"
       |"Sem⇩0 (com.lock n) C           = (λ σ. evs.lock n → C σ)"
       |"Sem⇩0 (com.unlock n) C         = (λ σ. evs.unlock n  → C σ)"
       |"Sem⇩0 (STORE E TO X⇩g⇩l⇩o) C       = (λ σ. update_glo X⇩g⇩l⇩o (E σ) → C σ)"
       |"Sem⇩0 (LOAD X⇩l⇩o⇩c FROM  X⇩g⇩l⇩o) C   = (λ σ. (λid. (read_glo X⇩g⇩l⇩o id))❙?x → C(σ(X⇩l⇩o⇩c:=x)))"
(* Fascinating: We don't need the sequential composition of CSP in this construction *)

find_theorems Sem⇩0
definition Sem         where ‹Sem Thread ≡ Sem⇩0 Thread (λ_. Skip) (λ_. 0)›  
           ― ‹final continuation: \<^term>‹Skip›, execution starts with initialized thread local vars.›

section‹A Thread-System as HOL-CSPM-Architecture›

text‹Now, wrapping all this up gives us:›

(*definition "σ⇩0" :: "σ" where ‹σ⇩0 ≡ (λ _. 0)›                           
           ― ‹initial state of variables›

definition SEMAPHORES where ‹SEMAPHORES idx ≡ Renaming (semaphore idx) Inl id›
           ― ‹lifting semaphores to the global alphabet›        
definition GLOBALVARS where ‹GLOBALVARS idx ≡ Renaming (global_vars idx σ⇩0) Inr id›
           ― ‹lifting global variables to the global alphabet›
           ― ‹attention: global state uninitialized›
(*Modifications*)
definition LOCALVARS where
  ‹LOCALVARS idx ≡ Renaming (locals_vars idx σ⇩0) Inr id›*)

definition SEMAPHORES where ‹SEMAPHORES idx ≡ Renaming (semaphore idx) id id›
           ― ‹lifting semaphores to the global alphabet›   

(*definition GLOBALVARS where
  ‹GLOBALVARS idx σ⇩0 ≡ Renaming (global_vars idx σ⇩0) Inr id›*)

definition GLOBALVARS ::
  "σ ⇒ string ⇒ (evs, unit) process⇩p⇩t⇩i⇩c⇩k"
where
  ‹GLOBALVARS σ⇩0 idx ≡ Renaming (global_vars σ⇩0 idx) (λx. x) (λy. y)›

definition LOCALVARS where
  "LOCALVARS  σ⇩0 idx ≡ Renaming (locals_vars  σ⇩0 idx)(λx. x) (λy. y)"

text‹An example of a global ‹IMP⇩c⇩o⇩n⇩c⇩u⇩r›-System with 2 threads, 3 global variables and 4 semaphores:›
definition my_initial_state :: σ where
  "my_initial_state v ≡ if v = ''a'' then 3 else 0"

term ‹( ❙|❙|❙| idx ∈# mset [''a'',''b'',''c''].  GLOBALVARS my_initial_state idx  )
      ⟦UNIV⟧ 
      (Sem(Thread1) ||| Sem(Thread2))
      ⟦UNIV⟧
      ( ❙|❙|❙| idx ∈# mset [1..4]. SEMAPHORES idx )›
definition Thread3_sem where 
"Thread3_sem = ( ❙|❙|❙| idx ∈# mset [''a'',''b'',''c''].  GLOBALVARS my_initial_state idx  )
      ⟦UNIV⟧ 
      (Sem(Thread1) ||| Sem(Thread2))
      ⟦UNIV⟧
      ( ❙|❙|❙| idx ∈# mset [1..4]. SEMAPHORES idx )"
(*
term ‹( ❙|❙|❙| idx ∈# mset [''a'',''b'',''c''].  GLOBALVARS idx )
      ⟦UNIV⟧ 
      (Sem(Thread1) ||| Sem(Thread2))
      ⟦UNIV⟧
      ( ❙|❙|❙| idx ∈# mset [1..4]. SEMAPHORES idx )›
ML‹
   val temp= \<^term>‹( ❙|❙|❙| idx ∈# mset [''a'',''b'',''c''].  GLOBALVARS idx )
      ⟦UNIV⟧ 
      (Sem(Thread1) ||| Sem(Thread2))
      ⟦UNIV⟧
      ( ❙|❙|❙| idx ∈# mset [1..4]. SEMAPHORES idx )›  
 val temp2= \<^term>‹❙|❙|❙| idx ∈# mset [''a'',''b'',''c''].  GLOBALVARS idx›

›*)
text‹TODO : A better approach to the tinkering with the renaming of alphabets would be locales ...›

text‹Tests:›
(*
schematic_goal H : "Sem(Thread2) = ?X"
  unfolding Thread2_def Sem_def
  apply(rule trans)
  apply simp
  apply (rule refl)
  done

schematic_goal K : "Thread3_sem = ?X"
  unfolding Thread3_sem_def Sem_def
  unfolding Thread1_def Thread2_def
   apply(rule trans)
  apply simp
  apply (rule refl)
  done

ML‹
val x =HOLogic.dest_eq (HOLogic.dest_Trueprop ( Thm.concl_of  @{thm K})) ; 
val x = @{thm K} |> Thm.concl_of 
                |> HOLogic.dest_Trueprop 
                |> HOLogic.dest_eq
›*)
end
