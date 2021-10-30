text\<open> 21 October 2021: Exercise for Homework Assignment 07 in CS 511 \<close> 
text\<open> Your task to remove the invocations of the pre-defined method 
      'blast' by an equivalent sequence of 'apply' steps \<close>

theory HW07_solution
  imports Main
begin

text\<open> 'blast' is invoked three times, once in the proof of each of
      lemmas B1, C1, and D1 below \<close>

(* the proof of the next lemma is just an example of how to use the
   rules for manipulating quantifiers *)
lemma preliminary : "(\<exists>z. P z) \<and> Q \<longrightarrow> (\<exists>y. P y \<and> Q)"
apply (rule impI)
apply (erule conjE)
apply (erule exE)
apply (rule_tac x="z" in exI)
apply (rule conjI)
apply assumption+
done

(* lemma A1 is the same in Exercise 2.3.9 (a), page 161, in [LCS] *)
lemma A1 : "(\<exists>x. S \<longrightarrow> Q x) \<Longrightarrow> S \<longrightarrow> (\<exists>x. Q x)" 
  apply (erule exE)
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply (rule_tac x="x" in exI)
  apply assumption
  done

(* lemma A2 is the same as lemma A1 but with a different proof *)
lemma A2 : "(\<exists>x. S \<longrightarrow> Q x) \<Longrightarrow> S \<longrightarrow> (\<exists>x. Q x)" 
  apply clarify
  apply (rule_tac x="x" in exI)
  apply assumption
  done

(* lemma B1 is the same in Exercise 2.3.9 (b), page 161, in [LCS] *)
lemma B1 : "S \<longrightarrow> (\<exists>x. Q x) \<Longrightarrow> (\<exists>x. S \<longrightarrow> Q x)"
  apply (erule exE)
  apply clarify
    apply (erule_tac x in exE)
  apply clarify
  apply (erule impE)
  apply (erule exE)
  apply (rule_tac x="x" in exI)
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply assumption
  by blast
    apply (rule impI)
  apply (erule impE)
   apply assumption
  by blast

(* lemma C1 is the same in Exercise 2.3.9 (c), page 161, in [LCS] *)
lemma C1 : "(\<exists>x. P x) \<longrightarrow> S \<Longrightarrow> \<forall>x. (P x \<longrightarrow> S)"
  apply (rule allI)
  apply (rule impI)
  apply (erule impE)
   apply (rule_tac x="x" in exI)
   apply assumption
  apply assumption
  done

(* lemma D1 is the same in Exercise 2.3.9 (d), page 161, in [LCS] *)
lemma D1 : " (\<forall>x. P x) \<longrightarrow> S \<Longrightarrow> \<exists>x. (P x \<longrightarrow> S)"
  apply (rule_tac x="z" in exI)
  by blast
  apply (erule impE)
  apply clarify
  apply (rule impI)
  apply (erule impE)
  apply assumption
   apply (erule_tac x="x" in allE)
  
  apply (drule spec)
  apply (rule impI)
  apply (erule impE)

end