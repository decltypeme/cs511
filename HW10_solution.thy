text\<open> 12 November 2021: Exercises for Homework 10 in CS 511 \<close> 
text\<open> Your task to remove the invocations of the pre-defined method 
      'blast' by an equivalent sequence of 'apply' steps \<close>

theory HW10_solution
  imports Main
begin

text\<open> 'blast' is invoked four times, once in the proof of each of
      lemmas E1, F1, G1, and H1 below \<close>

(* lemma E1 is the same in Exercise 2.3.9 (e), page 161, in [LCS] *)
lemma E1 : "\<forall> x. (P x \<or> Q x) \<Longrightarrow> (\<forall> x. P x) \<or> (\<exists> x. Q x)" 
  apply clarify
  apply (erule_tac x="x" in allE)
  apply (erule disjE)
   apply assumption
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply assumption
  done
  

(* lemma F1 is the same in Exercise 2.3.9 (f), page 161, in [LCS] *)
lemma F1 : "\<forall> x. \<exists> y. (P x \<or> Q y) \<Longrightarrow> \<exists> y. \<forall> x. (P x \<or> Q y)" 
  apply (rule exCI , rule allI)
  apply (erule_tac x="x" in allE)
  apply (rotate_tac 1, erule exE)
  apply (erule_tac x="y" in allE)
  apply (erule disjE, rule disjI1, assumption)
  apply (rule disjI2, erule notE, rule allI)
  apply (rule disjI2, assumption)
  done

(* lemma G1 is the same in Exercise 2.3.9 (g), page 161, in [LCS] *)
lemma G1 : "\<forall> x. (\<not> P x \<and> Q x) \<Longrightarrow> (\<forall> x. P x \<longrightarrow> Q x)" 
  apply (rule allI)
  apply (rule impI)
  apply (erule_tac x="x" in  allE)
  apply (erule conjE)
  apply assumption
  done
  

(* lemma H1 is the same in Exercise 2.3.9 (h), page 161, in [LCS] *)
lemma H1 : "\<forall> x. (P x \<and> Q x) \<Longrightarrow> (\<forall> x. P x \<longrightarrow> Q x)" 
  apply (rule allI)
  apply (rule impI)
  apply (erule_tac x="x" in allE)
  apply (erule conjE)
  apply assumption
  done

end