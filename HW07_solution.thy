text\<open> 21 October 2021: Exercise for Homework Assignment 07 in CS 511 \<close> 
text\<open> Your task to remove the invocations of the pre-defined method 
      'blast' by an equivalent sequence of 'apply' steps \<close>

theory HW07_solution
  imports Main
begin

text\<open> 'blast' is invoked three times, once in the proof of each of
      lemmas B1, C1, and D1 below \<close>

(* The proof of the next lemma is just an example of how to use the
   rules for manipulating quantifiers *)
lemma preliminary : " (\<exists>z. P z) \<and> Q \<longrightarrow> (\<exists>y. P y \<and> Q)"
apply (rule impI)
apply (erule conjE)
apply (erule exE)
apply (rule_tac x="z" in exI)
apply (rule conjI)
apply assumption+
done

(* Lemma A1 is the same in Exercise 2.3.9 (a), page 161, in [LCS] *)
lemma A1 : "(\<exists>x. S \<longrightarrow> Q x) \<Longrightarrow> S \<longrightarrow> (\<exists>x. Q x)" 
  apply (erule exE)
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply (rule_tac x="x" in exI)
  apply assumption
  done

(* Lemma A2 is the same as lemma A1 but with a different proof *)
lemma A2 : "(\<exists>x. S \<longrightarrow> Q x) \<Longrightarrow> S \<longrightarrow> (\<exists>x. Q x)" 
  apply clarify
  apply (rule_tac x="x" in exI)
  apply assumption
  done

(* Lemma B1 is the same in Exercise 2.3.9 (b), page 161, in [LCS] *)
lemma B1 : "S \<longrightarrow> (\<exists>x. Q x) \<Longrightarrow> (\<exists>x. S \<longrightarrow> Q x)" 
  by blast

text \<open>
lemma B1_by_Mattia : "S \<longrightarrow> (\<exists>x. Q x) \<Longrightarrow> (\<exists>x. S \<longrightarrow> Q x)"
	apply(rule_tac x="x" in exI)  (* Sledgehammer fails or says it is unprovable *)
	apply(rule impI)
	apply(erule impE)
	 apply assumption
	apply(erule exE)
\<close>
text\<open> Note: Copying in the secondary windows/panels works via the keyboard shortcuts 
  Ctrl+c or Ctrl+INSERT, while jEdit menu actions always refer to the primary windown/panel. \<close>

text\<open> The proof below consists of 'apply' steps only. The inserted comment
      after every step is the resulting 'proof state'. This proof is not
      the shortest or the most elegant, but understanding every step is a
      good exercise for how to apply the available pre-defined rules. \<close>
lemma B2 : "S \<longrightarrow> (\<exists>x. Q x) \<Longrightarrow> (\<exists>x. S \<longrightarrow> Q x)" 
  apply (rule exCI)  
(* S \<longrightarrow> (\<exists>x. Q x) \<Longrightarrow> \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> S \<longrightarrow> Q ?a *)
  apply (erule impE)
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> S
    2. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<longrightarrow> Q ?a *)
   apply (erule allE)
(*  1. \<not> (S \<longrightarrow> Q ?x5) \<Longrightarrow> S
    2. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<longrightarrow> Q ?a *)
   apply (rule contrapos_np)
(*  1. \<not> (S \<longrightarrow> Q ?x5) \<Longrightarrow> \<not> ?Q7
    2. \<not> (S \<longrightarrow> Q ?x5) \<Longrightarrow> \<not> S \<Longrightarrow> ?Q7
    3. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<longrightarrow> Q ?a *)
    apply assumption
(*  1. \<not> (S \<longrightarrow> Q ?x5) \<Longrightarrow> \<not> S \<Longrightarrow> S \<longrightarrow> Q ?x5
    2. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<longrightarrow> Q ?a *)
   apply (rule impI)
(*  1. \<not> (S \<longrightarrow> Q ?x5) \<Longrightarrow> \<not> S \<Longrightarrow> S \<Longrightarrow> Q ?x5
    2. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<longrightarrow> Q ?a *)
   apply (erule notE)+
(*  1. S \<Longrightarrow> S
    2. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<longrightarrow> Q ?a *)
   apply assumption
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<longrightarrow> Q ?a *)
  apply (rule impI)
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> Q ?a *)
  apply (rule notE) 
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> \<not> ?P18
    2. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> ?P18 *)
   apply (rule notI) 
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> ?P18 \<Longrightarrow> False
    2. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> ?P18 *)
   apply (erule FalseE) 
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> False *)
  apply (rule contrapos_np)
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> \<not> ?Q24
    2. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> \<not> False \<Longrightarrow> ?Q24 *)
   apply (rule notI)
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> ?Q24 \<Longrightarrow> False
    2. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> \<not> False \<Longrightarrow> ?Q24 *)
   apply (erule notE)
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> ?P29
    2. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> \<not> False \<Longrightarrow> \<not> ?P29 *)
   apply assumption
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> \<not> False \<Longrightarrow> \<not> (\<forall>x. \<not> (S \<longrightarrow> Q x)) *)
  apply (rule notI)
(*  1. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> \<exists>x. Q x \<Longrightarrow> S \<Longrightarrow> \<not> False \<Longrightarrow> \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> False *)
  apply (erule exE)
(*  1. \<And>x. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> S \<Longrightarrow> \<not> False \<Longrightarrow> \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> Q x \<Longrightarrow> False *)
  apply (erule notE) 
(*  1. \<And>x. \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> S \<Longrightarrow> \<forall>x. \<not> (S \<longrightarrow> Q x) \<Longrightarrow> Q x \<Longrightarrow> False *)
  apply (erule allE)+ 
(*  1. \<And>x. S \<Longrightarrow> Q x \<Longrightarrow> \<not> (S \<longrightarrow> Q (?x37 x)) \<Longrightarrow> \<not> (S \<longrightarrow> Q (?x39 x)) \<Longrightarrow> False *)
  apply (erule notE)+ 
(*  1. \<And>x. S \<Longrightarrow> Q x \<Longrightarrow> S \<longrightarrow> Q (?x39 x) *)
  apply (rule impI) 
(*  1. \<And>x. S \<Longrightarrow> Q x \<Longrightarrow> S \<Longrightarrow> Q (?x39 x) *)
  apply assumption
(* No subgoals! *)
  done
(* Lemma C1 is the same in Exercise 2.3.9 (c), page 161, in [LCS] *)
lemma C1 : "(\<exists>x. P x) \<longrightarrow> S \<Longrightarrow> \<forall>x. (P x \<longrightarrow> S)"
  by blast
text\<open> The proof below consists of 'apply' steps only. \<close>
lemma C2 : "(\<exists>x. P x) \<longrightarrow> S \<Longrightarrow> \<forall>x. (P x \<longrightarrow> S)"
  apply (rule allI)
  apply (rule impI)
  apply (erule impE)
  apply (rule_tac x="x" in exI)
   apply assumption+
  done

(* Lemma D1 is the same in Exercise 2.3.9 (d), page 161, in [LCS] *)
lemma D1 : " (\<forall>x. P x) \<longrightarrow> S \<Longrightarrow> \<exists>x. (P x \<longrightarrow> S)"
  by blast
text\<open> The proof below consists of 'apply' steps. The inserted comment
      after every step is the resulting 'proof state'. This proof is not
      the shortest or the most elegant, but understanding every step is a
      good exercise for how to apply the available pre-defined rules. \<close>
lemma D2 : " (\<forall>x. P x) \<longrightarrow> S \<Longrightarrow> \<exists>x. (P x \<longrightarrow> S)"
  apply (rule exCI)
(* 1. (\<forall>x. P x) \<longrightarrow> S \<Longrightarrow> \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> P ?a \<longrightarrow> S *)
  apply (erule impE)
(*  1. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> \<forall>x. P x
    2. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<longrightarrow> S *)
   apply (rule allI)
(*  1. \<And>x. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> P x
    2. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<longrightarrow> S *)
   apply (erule_tac x="x" in allE)
(*  1. \<And>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> P x
    2. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<longrightarrow> S *)
   apply  (rule contrapos_np)
(*  1. \<And>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> \<not> ?Q8 x
    2. \<And>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> \<not> P x \<Longrightarrow> ?Q8 x
    3. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<longrightarrow> S *)
    apply assumption
(*  1. \<And>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> \<not> P x \<Longrightarrow> P x \<longrightarrow> S
    2. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<longrightarrow> S *)
   apply (rule impI)
(*  1. \<And>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> \<not> P x \<Longrightarrow> P x \<Longrightarrow> S
    2. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<longrightarrow> S *)
   apply (erule notE)
(*  1. \<And>x. \<not> P x \<Longrightarrow> P x \<Longrightarrow> P x \<longrightarrow> S
    2. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<longrightarrow> S *)
   apply (rule impI)
(*  1. \<And>x. \<not> P x \<Longrightarrow> P x \<Longrightarrow> P x \<Longrightarrow> S
    2. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<longrightarrow> S *)
   apply (erule notE)
(*  1. \<And>x. P x \<Longrightarrow> P x \<Longrightarrow> P x
    2. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<longrightarrow> S *)
   apply assumption
(*  1. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<longrightarrow> S *)
  apply (rule impI)
(*  1. \<forall>x. \<not> (P x \<longrightarrow> S) \<Longrightarrow> S \<Longrightarrow> P ?a \<Longrightarrow> S *)
  apply assumption
(* No subgoals! *)
  done
end