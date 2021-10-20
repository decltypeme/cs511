text\<open> 8 October 2021: Exercise for Homework Assignment 06 in CS 511 \<close> 
text\<open> Your task to remove the invocation of the pre-defined method blast,
      by an equivalent sequence of 'apply' steps \<close>
text\<open> This is a continuation of the Isabelle exercise you did for
      Homework Assignment 05, and inspired by the exercise on page 32
      in Lecture Slides 11 "Quantified Propositional Logic" \<close>

theory HW06_solution
  imports Main
begin

(* The following is a theorem of QPL. Note that "=" means the same as "\<longleftrightarrow>" *)
theorem "(\<exists>y. (y = Phi) \<and> (y \<or> Psi1) \<and> (y \<or> Psi2)) \<longleftrightarrow> (Phi \<or> Psi1) \<and> (Phi \<or> Psi2)"
  apply (rule iffI)
  apply (erule exE)
  apply (erule conjE)
  apply clarify
  apply (rule exI)
  apply (clarify)
  apply (rule conjI)
  apply (rule iffI)
  apply clarify
  apply assumption
  apply clarify
  apply (rule conjI)
  apply assumption
  apply assumption 
  done 
end