theory CommOr
  imports Main

begin 

text\<open> Apply style \<close>
lemma lem_w_1 : "(p \<or> q) \<longrightarrow> (q \<or> p)"
  apply (rule impI)
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done

text\<open> Apply style proof, more verbose than the preceding proof \<close>
lemma lem_w_2 : "(p \<or> q) \<longrightarrow> (q \<or> p)"
  apply (rule impI)
  apply (rule disjE)
    apply assumption
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done

text\<open> Isar style \<close>
lemma lem_x_1 : "(p \<or> q) \<longrightarrow> (q \<or> p)"
proof   
  assume A : "(p \<or> q)" 
  from A show "(q \<or> p)"
  proof 
    assume "p" thus "(q \<or> p)" by (rule disjI2)
    (* you can substitute '..' for 'by (rule disjI2)'*)
  next
    assume "q" thus "(q \<or> p)" by (rule disjI1) 
    (* you can substitute '..' for 'by (rule disjI1)'*)
  qed
qed
end