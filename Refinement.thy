theory Refinement
imports AT
begin

(* Improvement possibility:
The first two conditions in mod_trans could be part of Kripke type_def and thus become implicit *)
definition refinement :: "[('a::state) kripke,('a'::state) \<Rightarrow> 'a, 'a' kripke] \<Rightarrow> bool" ("(_ \<sqsubseteq>\<^sub>_ _)" 50)  
  where "K \<sqsubseteq>\<^sub>E K' = (init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and>
    (\<forall> s' \<in> (states K'). (\<forall> s \<in> (init K'). (s \<rightarrow>\<^sub>i* s') \<longrightarrow> (E s) \<in> (init K) \<and> (E s) \<rightarrow>\<^sub>i* (E s'))))"

definition refinement' :: "[('a::state) kripke,('a'::state) \<Rightarrow> 'a, 'a' kripke] \<Rightarrow> bool" ("(_ \<subseteq>\<^sub>_ _)" 50)  
  where "K \<subseteq>\<^sub>E  K' = (init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and>
    (\<forall> s \<in> (states K').  \<forall> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s \<longrightarrow> ((E s0) \<rightarrow>\<^sub>i* (E s) \<and>
               (\<forall> s' \<in> (states K'). (s \<rightarrow>\<^sub>i s') \<longrightarrow> (E s) \<rightarrow>\<^sub>i* (E s')))))"

lemma ref_ref'_eq: "(K \<sqsubseteq>\<^sub>E K') = (K \<subseteq>\<^sub>E  K')"
  unfolding refinement_def refinement'_def
proof
  show \<open>init K' \<subseteq> states K' \<and>
    init K \<subseteq> states K \<and>
    (\<forall>s'\<in>states K'. \<forall>s\<in>init K'. s \<rightarrow>\<^sub>i* s' \<longrightarrow> E s \<in> init K \<and> E s \<rightarrow>\<^sub>i* E s') \<Longrightarrow>
    init K' \<subseteq> states K' \<and>
    init K \<subseteq> states K \<and>
    E ` init K' \<subseteq> init K \<and>
    (\<forall>s\<in>states K'.
        \<forall>s0\<in>init K'.
           s0 \<rightarrow>\<^sub>i* s \<longrightarrow> E s0 \<rightarrow>\<^sub>i* E s \<and> (\<forall>s'\<in>states K'. s \<rightarrow>\<^sub>i s' \<longrightarrow> E s \<rightarrow>\<^sub>i* E s'))\<close>
    apply (erule conjE)+
    apply (intro conjI, assumption+)
     apply (rule subsetI)
    (* seems not true*)
     prefer 2
     apply (rule ballI)+
     apply (rule impI)
     apply (rule conjI)
      apply force
     apply (rule ballI)
    apply (rule impI)
     apply (drule_tac x = s' in bspec, assumption)
     apply (drule_tac x = s0 in bspec, assumption)
    oops
(* the two notions of refinement seem not to imply each other!*)

theorem strong_ref'''[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> 
     (\<forall> s. \<forall> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s \<longrightarrow> (E s0) \<rightarrow>\<^sub>i* (E s) \<and> (\<forall> s'. s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i* (E s'))) \<Longrightarrow>
                                K \<subseteq>\<^sub>E K'"
  apply (unfold refinement'_def)
  by simp

lemma init_ref: "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> E ` (init K') \<subseteq> (init K)"
  apply (simp add: refinement_def)
  apply (rule subsetI)
  apply (erule imageE)
  apply (rotate_tac -2)
  apply (erule ssubst)
  apply (erule conjE)+
  apply (drule_tac x = xa in bspec)
  apply (erule subsetD, assumption)
  apply (drule_tac x = xa in bspec)
  apply assumption
  apply (erule impE)
  apply (simp add: state_transition_refl_def)
by (erule conjE, assumption)

(* This version allows that the init in the refinement "deletes" some initial states *)
theorem prop_pres:  "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> (\<forall> s' \<in> (Pow (states K')). 
                      (K' \<turnstile> EF s') \<longrightarrow> (Kripke (states K)(E ` (init K')) \<turnstile> EF (E ` s')))" 
  apply clarify
  apply (frule init_ref)
  apply (unfold refinement_def)
  apply (erule conjE)+
  apply (simp add: check_def)
  apply (rule subsetI)
  apply (rule CollectI)
  apply (rule conjI)
  apply (rule_tac A = "init K" in subsetD, assumption)
   apply (rule_tac A = "E ` init K'" in subsetD, assumption+)
  apply (subgoal_tac "? y. y \<in> init K' \<and> E y = x")
   prefer 2
  apply force
  apply (erule exE)
  apply (erule conjE)
   apply (rotate_tac 1)
   apply (drule subsetD, assumption)
   apply (erule CollectE)
  apply (erule conjE)
   apply (drule EF_step_star_rev)
  apply (erule bexE)
  apply (drule_tac x = ya in bspec)
  apply (erule subsetD, assumption)
  apply (drule_tac x = y in bspec, assumption)
  apply (drule mp, assumption)
  apply (erule conjE)
  apply (rule_tac y = "E ya" in EF_step_star)
   apply (erule subst, assumption)
by simp

(* In this version of the property preservation theorem, the init_ref condition is
   stronger so it will be disallowed to "delete" initial states during refinement. 
   Then the second more complex Kripke structure in prop_pres becomes simply K *)
lemma Kripke_self: "K = Kripke (states K) (init K)"
  apply (case_tac K)
by simp


theorem prop_pres':  "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> init K \<subseteq> E ` (init K') \<Longrightarrow> (\<forall> s' \<in> (Pow (states K')). 
                      (K' \<turnstile> EF s') \<longrightarrow> (K \<turnstile> EF (E ` s')))" 
  apply (subgoal_tac "init K = E ` (init K')")
   apply (subgoal_tac "K = Kripke (states K)(init K)")
  apply (rotate_tac -1)
  apply (erule ssubst)
    apply (erule ssubst)
  apply (rule prop_pres, assumption)
   apply (rule Kripke_self)
  apply (rule subset_antisym, assumption)
by (erule init_ref)

lemma image_lem: \<open>inj E \<Longrightarrow> E y \<in> (E ` s) \<Longrightarrow> y \<in> s\<close>
  by (simp add: inj_image_mem_iff)

(* Inverse prop pres for AG *)
theorem prop_presAG:  "inj E \<Longrightarrow> WF_Kripke K' \<Longrightarrow> K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> (\<forall> s \<in> (Pow (states K')). 
                      (K \<turnstile> AG(E ` s)) \<longrightarrow> (Kripke (states K')(init K') \<turnstile> AG (s)))"
  apply clarify
  apply (frule init_ref)
  apply (unfold refinement_def)
  apply (erule conjE)+
  apply (simp add: check_def)
  apply (rule subsetI)
  apply (rule CollectI)
  apply (rule conjI)
  apply blast
  apply (subgoal_tac \<open>E x \<in> init K\<close>)
  prefer 2
  apply blast
   apply (rotate_tac 1)
   apply (drule subsetD, assumption)
   apply (erule CollectE)
  apply (erule conjE)
(* *)
  apply (rule AG_all_sO)
  apply (rule allI, rule impI)
  apply (subgoal_tac \<open>E y \<in> E ` s\<close>)
   apply (erule image_lem, assumption)
  apply (subgoal_tac \<open>E x \<rightarrow>\<^sub>i* E y\<close>)
   apply (metis AG_all_s AG_in_lem)
  apply (drule_tac x = y in bspec)
  apply (simp add: state_transition_refl_def)
   apply (unfold image_def)
   prefer 2
   apply fastforce
  by (simp add: WF_Kripke_def state_transition_refl_def)

(* Not valid *) 
theorem prop_presAF:  "K \<sqsubseteq>\<^sub>E K' \<Longrightarrow> (\<forall> s' \<in> (Pow (states K')). 
                      (K' \<turnstile> AF s') \<longrightarrow> (Kripke (states K)(E ` (init K')) \<turnstile> AF (E ` s')))" 
  apply clarify
  apply (frule init_ref)
  apply (unfold refinement_def)
  apply (erule conjE)+
  apply (simp add: check_def)
  apply (rule subsetI)
  apply (rule CollectI)
  apply (rule conjI)
  apply (rule_tac A = "init K" in subsetD, assumption)
   apply (rule_tac A = "E ` init K'" in subsetD, assumption+)
  apply (subgoal_tac "? y. y \<in> init K' \<and> E y = x")
   prefer 2
  apply force
  apply (erule exE)
  apply (erule conjE)
   apply (rotate_tac 1)
   apply (drule subsetD, assumption)
   apply (erule CollectE)
  apply (erule conjE)
(* Need to apply an equivalent of the following*)
(*    apply (drule EF_step_star_rev) : ?x \<in> EF ?s \<Longrightarrow> \<exists>y\<in>?s. ?x \<rightarrow>\<^sub>i* y*)

  oops

(* For refinement' *)
lemma init_ref_ref: "K \<subseteq>\<^sub>E K' \<Longrightarrow> E ` (init K') \<subseteq> (init K)"
  by (simp add: refinement'_def)
 
theorem prop_pres_ref:  "K \<subseteq>\<^sub>E K' \<Longrightarrow> (\<forall> s' \<in> (Pow (states K')). 
                      (K' \<turnstile> EF s') \<longrightarrow> (Kripke (states K)(E ` (init K')) \<turnstile> EF (E ` s')))" 
  apply clarify
  apply (frule init_ref_ref)
  apply (unfold refinement'_def)
  apply (erule conjE)+
  apply (simp add: check_def)
  apply (rule subsetI)
  apply (rule CollectI)
  apply (rule conjI)
   apply blast
  apply (subgoal_tac "? y. y \<in> init K' \<and> E y = x")
   prefer 2
  apply force
  apply (erule exE)
  apply (erule conjE)
   apply (rotate_tac 1)
   apply (drule subsetD, assumption)
   apply (erule CollectE)
  apply (erule conjE)
   apply (drule EF_step_star_rev)
  apply (erule bexE)
  apply (drule_tac x = ya in bspec)
  apply (erule subsetD, assumption)
  apply (drule_tac x = y in bspec, assumption)
  apply (drule mp, assumption)
  apply (rule_tac y = "E ya" in EF_step_star)
  apply fastforce
 by simp


theorem strong_mt[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> (\<forall> s s'. s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i (E s')) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  apply (unfold refinement_def)
  apply simp
  apply (erule conjE)+
  apply (rule ballI)+
  apply (rule impI)
  apply (rule conjI)
   apply (erule subsetD)
   apply (erule imageI)
  apply (subgoal_tac "(\<forall>s::'a. s \<rightarrow>\<^sub>i s' \<longrightarrow> E s \<rightarrow>\<^sub>i E s') \<longrightarrow> s \<rightarrow>\<^sub>i* s' \<longrightarrow> E s \<rightarrow>\<^sub>i* E s'")
   apply simp
  apply (simp add: state_transition_refl_def)
  apply (erule_tac rtrancl_induct)
   apply simp
  apply (drule_tac x = y in spec)
  apply (drule_tac x = z in spec)
  apply (drule mp, simp)
  apply (erule rtrancl_into_rtrancl)
  apply (rule CollectI)
  by simp

theorem strong_mt'[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> 
     (\<forall> s s'. (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i (E s')) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  apply (unfold refinement_def)
  apply simp
  apply (erule conjE)+
  apply (rule ballI)+
  apply (rule impI)
  apply (rule conjI)
   apply (erule subsetD)
   apply (erule imageI)
  apply (subgoal_tac "(\<forall>s::'a. (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i s' \<longrightarrow> E s \<rightarrow>\<^sub>i E s') \<longrightarrow> 
                                  (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i* s' \<longrightarrow> E s \<rightarrow>\<^sub>i* E s'")
   apply simp
   apply (erule mp)
   apply (rule_tac x = s in bexI)
    apply (simp add: state_transition_refl_def, assumption)
     apply (simp add: state_transition_refl_def)
  apply (erule_tac rtrancl_induct)
   apply simp
  apply (rule impI)
  apply (drule mp)
  apply assumption
   apply (drule_tac x = y in spec)
(* *)
  apply (rotate_tac -1)
   apply (drule mp)
    apply (rule_tac x = s in bexI)
  apply assumption+
  apply (erule rtrancl_into_rtrancl)
   apply (rule CollectI)
by simp

theorem strong_mt''[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> 
     (\<forall> s s'. (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i* (E s')) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  apply (unfold refinement_def)
  apply simp
  apply (erule conjE)+
  apply (rule ballI)+
  apply (rule impI)
  apply (rule conjI)
   apply (erule subsetD)
   apply (erule imageI)
  apply (subgoal_tac "(\<forall>s::'a. (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i s' \<longrightarrow> E s \<rightarrow>\<^sub>i* E s') \<longrightarrow> 
                                  (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s) \<longrightarrow> s \<rightarrow>\<^sub>i* s' \<longrightarrow> E s \<rightarrow>\<^sub>i* E s'")
   apply simp
   apply (erule mp)
   apply (rule_tac x = s in bexI)
    apply (simp add: state_transition_refl_def, assumption)
     apply (simp add: state_transition_refl_def)
  apply (erule_tac rtrancl_induct)
   apply simp
  apply (rule impI)
  apply (drule mp)
  apply assumption
  apply (drule_tac x = y in spec)
  apply (rotate_tac -1)
   apply (drule mp)
    apply (rule_tac x = s in bexI)
    apply assumption+
  thm rtrancl_trans
  apply (erule rtrancl_trans)
by simp

(* slightly nicer way of putting the quantors in strong_mt''*)
theorem strong_mt''a[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> 
     (\<forall> s. \<forall> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s \<longrightarrow> (\<forall> s'. s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i* (E s'))) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  by (simp add: strong_mt'')

(* If we add the reachability of the abstract to the assumptiosn, we need
   to apply induction because s \<rightarrow>\<^sub>i* s' instead of s \<rightarrow> s'*)
theorem strong_mt'''O[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> 
     (\<forall> s. \<forall> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s \<longrightarrow> (E s0) \<rightarrow>\<^sub>i* (E s) \<longrightarrow> (\<forall> s'. s \<rightarrow>\<^sub>i* s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i* (E s'))) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  apply (unfold refinement_def)
  apply (erule conjE)+
  apply (intro conjI, assumption+)
  apply simp
  apply (rule ballI)+
  apply (rule impI)
  apply (rule conjI)
  apply blast
  apply (drule_tac x = s in spec)
  apply (drule_tac x = s in bspec)
  apply simp
  apply (drule mp)
  apply (meson rtrancl.intros(1) state_transition_refl_def)
  by (simp add: state_transition_refl_def)


(* Not true when the * in s \<rightarrow> s' is left out *)
theorem strong_mt'''[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> 
     (\<forall> s s'. (\<exists> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s \<and> (E s0) \<rightarrow>\<^sub>i* (E s)) \<longrightarrow> s \<rightarrow>\<^sub>i s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i* (E s')) \<Longrightarrow>
                                K \<sqsubseteq>\<^sub>E K'"
  oops 

(* The alternative formulation of refinement' doesn't give us any more.
   Still need to explore what is the actual difference between the two 
   refinements.*)
theorem strong_mt'''OO[rule_format]: 
"init K' \<subseteq> states K' \<and> init K \<subseteq> states K \<and> E ` (init K') \<subseteq> (init K) \<and> 
     (\<forall> s. \<forall> s0 \<in> init K'. s0  \<rightarrow>\<^sub>i* s \<longrightarrow> (E s0) \<rightarrow>\<^sub>i* (E s) \<longrightarrow> (\<forall> s'. s \<rightarrow>\<^sub>i* s' \<longrightarrow> (E s) \<rightarrow>\<^sub>i* (E s'))) \<Longrightarrow>
                                K \<subseteq>\<^sub>E K'"
  apply (unfold refinement'_def)
  apply (erule conjE)+
  apply (intro conjI, assumption+)
  apply simp
  apply (rule ballI)+
  apply (rule impI)
  apply (rule conjI)
  apply (drule_tac x = s in spec)
  apply (drule_tac x = s0 in bspec)
  apply simp
  apply (drule mp)
    apply (meson rtrancl.intros(1) state_transition_refl_def)
  prefer 2
  apply (simp add: state_transition_refl_def)
   apply (simp add: r_into_rtrancl)
(* remains: 
    ... s0 \<rightarrow>\<^sub>i* s \<Longrightarrow> E s0 \<rightarrow>\<^sub>i* E s \<longrightarrow> (\<forall>s'. s \<rightarrow>\<^sub>i* s' \<longrightarrow> E s \<rightarrow>\<^sub>i* E s') \<Longrightarrow> E s0 \<rightarrow>\<^sub>i* E s
   which says that we cannot assume E s0 \<rightarrow>\<^sub>i* E s but rather need to prove it with this
   definition *)
  oops
(* We don't need to show that previous level did have an attack:
   the (K \<turnstile> EF (E `s)) 
definition RR_cycle :: "[('a::state) kripke, ('a'::state)kripke, 'a' set] \<Rightarrow> bool"
  where "RR_cycle K K' s = (\<exists> (E:: ('a'::state) \<Rightarrow> 'a). (K \<turnstile> EF (E `s)) \<and> (K \<sqsubseteq>\<^sub>E K') \<and> \<not>(K' \<turnstile> EF s))"
*)

definition RR_cycle :: "[('a::state) kripke, ('a'::state)kripke, 'a' set] \<Rightarrow> bool"
  where "RR_cycle K K' s = (\<exists> (E:: ('a'::state) \<Rightarrow> 'a). (K \<sqsubseteq>\<^sub>E K') \<and> \<not>(K' \<turnstile> EF s))"

definition RR_cycleO :: "[('a'::state)kripke, 'a' set] \<Rightarrow> bool"
  where "RR_cycleO K' s = 
 (\<exists> (K :: ('a::state)kripke). (\<exists> (E:: ('a'::state) \<Rightarrow> 'a). (K \<sqsubseteq>\<^sub>E K') \<and> \<not>(K' \<turnstile> EF s)))"


(* This statement says that if globally a property -s holds in a model 
   (and we think of this as "no attacks = s is not reachable = global policy holds") 
   then there is no more RR cycle refinement.  *)
lemma RR_cycle_stopO: \<open>I \<noteq> {} \<Longrightarrow> ((Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I  \<turnstile> AG (-s))) \<Longrightarrow> 
                     RR_cycle (Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I)(Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I) s\<close>
  apply (drule AG_imp_notnotEF, assumption)
  apply (subgoal_tac \<open>(- (- s)) = s\<close>)
  apply simp
   apply (unfold RR_cycle_def)
   apply (rule_tac x = id in exI)
  apply (simp add: check2_def refinement_def)
  by blast

(* Or equivalently RR-cycle holds already for this model because 
   "no attacks to s" = not(EF s) = RR_cycle  *)
lemma RR_cycle_stopOO: \<open>I \<noteq> {} \<Longrightarrow> \<not>((Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I  \<turnstile> EF s)) \<Longrightarrow> 
                     RR_cycle (Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I)(Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I) s\<close>
  apply (simp add: RR_cycle_def)
   apply (rule_tac x = id in exI)
  by (metis (no_types, lifting) CollectI id_apply init.simps refinement_def rtrancl.intros(1) state_transition_refl_def states.simps subset_eq)

(* What does this lemma say? It only says that if in ((Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I
   globally holds that s then also ((Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I |- EF s
   therefore (def of RR_cycle) clearly NOT \<not>(... |- EF s).
   It's meaningless here better delete. *)
lemma RR_cycle_stop: \<open>I \<noteq> {} \<Longrightarrow> ((Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I  \<turnstile> AG s)) \<Longrightarrow>
                     \<not>(RR_cycle K (Kripke {s. \<exists> i \<in> I. (i \<rightarrow>\<^sub>i* s)} I) s)\<close>
  apply (drule AG_imp_notnotEF, assumption)
  apply (unfold RR_cycle_def)
  apply (rule notI)
  apply (erule exE)
  apply (erule conjE)+
  by (smt (verit) AG_in_lem EF_lem2d Int_iff check2_def subset_eq)

end

