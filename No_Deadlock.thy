theory No_Deadlock
  imports IMP_CONCUR
begin

fun well_bracketed :: "com \<Rightarrow> MV set \<Rightarrow> bool" where
  "well_bracketed SKIP _ = True"
| "well_bracketed (LOCAL v := e) _ = True"
| "well_bracketed (c1 ; c2) ms = (well_bracketed c1 ms \<and> well_bracketed c2 ms)"
| "well_bracketed (IF b THEN c1 ELSE c2) ms = (well_bracketed c1 ms \<and> well_bracketed c2 ms)"
| "well_bracketed (WHILE b DO c) ms = well_bracketed c ms"
| "well_bracketed (lock m) ms = (m \<notin> ms)"
| "well_bracketed (unlock m) ms = True"
| "well_bracketed (_ \<hookrightarrow> _) _ = True"
| "well_bracketed (_ \<hookleftarrow> _) _ = True"

(* Définit si une config est bloquée : aucune règle ne peut s'appliquer *)
definition deadlocked :: "config \<Rightarrow> bool" where
  "deadlocked cfg \<equiv> \<not> (\<exists>cfg'. cfg \<mapsto> cfg')"

(* Théorème d'absence de deadlock si usage correct des mutex *)
theorem no_deadlock_for_well_bracketed:
  assumes "well_bracketed c {}"
  shows   "\<not> deadlocked (c, \<sigma>, s)"
proof (induction c arbitrary: \<sigma> s)
  case SKIP
  then show ?case
    by (simp add: deadlocked_def)
next
  case (assign v e)
  then show ?case
    by (auto simp: deadlocked_def)
next
  case (seq c1 c2)
  then show ?case
  proof (cases c1)
    case SKIP
    then show ?thesis
      using Step_Seq1 deadlocked_def by blast
  next
    case (assign v e)
    then show ?thesis
      using Step_Seq2 Step_Assign deadlocked_def seq by fastforce
  qed (auto simp: deadlocked_def intro: Step_Seq2)
next
  case (cond b c1 c2)
  then show ?case
    using Step_If_True Step_If_False deadlocked_def by auto
next
  case (while b c)
  then show ?case
    using Step_While deadlocked_def by auto
next
  case (lock m)
  then show ?case
    using Step_Lock deadlocked_def well_bracketed.simps by auto
next
  case (unlock m)
  then show ?case
    using Step_Unlock deadlocked_def by auto
next
  case (send svar e)
  then show ?case
    using Step_Send deadlocked_def by auto
next
  case (rec v svar)
  then show ?case
    using Step_Rec deadlocked_def by auto
qed

end