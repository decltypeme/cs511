theory HealthyOrIll
  imports Main

begin 

text\<open> Apply style \<close>
theorem healthy_ill : "(healthy \<or> ill) \<and> (healthy \<longrightarrow> travel) \<and> \<not>ill \<longrightarrow> travel"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
  apply (erule conjE)
  apply (erule impE)
  apply assumption
  apply assumption
  apply (erule conjE)
  apply (erule impE)
  apply (erule notE)
  apply assumption
  apply assumption
  done
end