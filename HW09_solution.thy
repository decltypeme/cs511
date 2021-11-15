text\<open> 4 Nov 2021: Two lemmas for Homework 09 in CS 511 \<close> 
text\<open> In the first lemma A1, your task to remove the invocation of the 
      pre-defined method 'blast' by an equivalent sequence of 'apply' steps \<close>
text\<open> In the second lemma B1, your task is to shorten the given proof \<close>

theory HW09_solution
  imports Main
begin

text \<open> Exercise 1 on the last page of Lecture Slides 28, Analytic Tableaux
       Part I  \<close>

lemma A1 : " (\<forall>x. \<forall>y. \<forall>z. P(x,y) \<and> P(y,z) \<longrightarrow> P(x,z)) \<and> (\<forall>x. \<forall>y. P(x,y) \<longrightarrow> P(y,x)) 
            \<Longrightarrow> \<forall>x. \<forall>y. \<forall>z. P(x,y) \<and> P(z,y) \<longrightarrow> P(x,z) "
  apply (rule allI)+
  apply (rule impI)
  apply (erule conjE)+
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="z" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="z" in allE)
  apply (erule mp)
  apply (rule conjI)
   apply assumption
  apply (erule mp)
  apply assumption
done

text \<open> Exercise 2 on the last page of Lecture Slides 28, Analytic Tableaux
       Part I  \<close>
lemma B1 : " \<forall>x. Q(a,x,x) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> 
    Q(x,s(y),s(z))) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> Q(y,x,z)) \<Longrightarrow> \<exists> x. Q( s(s(a)), s(s(s(a))), x)"
  by blast

text \<open> Below is a proof of lemma B2 consisting of 26 'apply' steps. It includes many
       unnecessary steps. For full credit, produce a proof with at most 20 'apply' steps. \<close>
lemma B2 : "(\<forall>x. Q(a,x,x)) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> 
    Q(x,s(y),s(z))) \<and> (\<forall>x y z. Q(x,y,z) \<longrightarrow> Q(y,x,z)) \<Longrightarrow> \<exists> x. Q( s(s(a)), s(s(s(a))), x)"
  apply (erule conjE)+
  apply (rule_tac x="s(s(s(s(s(a)))))" in exI)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="a" in allE)
  apply (frule_tac x="a" in spec)
  apply (frule_tac x="s(a)" in spec)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule_tac x="s(s(s(a)))" in allE)
  apply (erule_tac x="s(s(s(s(a))))" in allE)
  apply (erule_tac x="s(s(a))" in allE)
  apply (erule impE)
  apply (erule mp)
  apply assumption
  apply (erule mp)+
  apply assumption
  done

end