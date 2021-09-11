theory CommAnd
  imports Main

begin 

text\<open> Apply style \<close>
lemma lem_k_1 : "(p \<and> q) \<longrightarrow> (q \<and> p)"
  apply (rule impI)
  apply (rule conjI)
  apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

text\<open> Isar style, the proof illustrates the use of intermediate facts,
   once more with keywords 'from ... have ...' \<close>
lemma lem_l_1 : "(p \<and> q) \<longrightarrow> (q \<and> p)"
proof
  assume a : "p \<and> q"
  from a have b : "p" by (rule conjE)     (* INTERMEDIATE fact *)
  from a have c : "q" by (rule conjE)     (* INTERMEDIATE fact *)
  from c b show "q \<and> p" by (rule conjI)   (* we must write 'from c b' not 'from b c' *)
qed

text\<open> Isar style, lem_l_1 again, with more abbreviations \<close>
lemma lem_l_2 : "(p \<and> q) \<longrightarrow> (q \<and> p)"
proof
  assume a : "p \<and> q"
  from a have b : "p" ..
  from a have c : "q" ..
  from c b show "(q \<and> p)" ..
qed

text\<open> Isar style, lem_l_1 again, with nested proofs \<close>
lemma lem_l_3 : "(p \<and> q) \<longrightarrow> (q \<and> p)"
proof
  assume a : "p \<and> q"
  from a show "q \<and> p"
  proof
    assume b : "p"
    assume c : "q"
    from c b show "q \<and> p" by (rule conjI)
  qed
qed
end