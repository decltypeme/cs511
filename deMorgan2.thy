theory deMorgan2
  imports Main

begin 

text\<open> Apply style \<close>
theorem de_morgan_2 : "((\<not> p \<and> \<not> q)  \<longrightarrow> (\<not> (p \<or> q)))"
  apply (rule impI)
  apply (rule notI)
  apply (erule disjE)
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  apply (erule conjE)
  apply (erule notE)
  apply (erule notE)
  apply assumption
  done
end