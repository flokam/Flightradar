theory IFC
  imports "../Refinement"
begin

declare [[show_types]]
declare [[show_sorts]]

definition MLS_order :: "('a :: linorder \<times> 'b :: lattice) \<Rightarrow> 
                         (('a \<Rightarrow> 'a  \<Rightarrow> bool) \<times> ('b \<Rightarrow> 'b \<Rightarrow> bool))
                          \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool"
("(_ \<preceq>\<^sub>_ _)" 50)
where
"(pOsO) \<preceq>\<^sub>lopo (p1s1) = 
((fst lopo (fst pOsO)(fst p1s1)) \<and> (snd lopo (snd (pOsO))(snd(p1s1))))"

(* Example from D. Gollmann's book*)
typedef pupr = "{''public'', ''private''}"
by (rule_tac x = "''public''" in exI, simp) 

definition pupr_le :: "pupr \<Rightarrow> pupr \<Rightarrow> bool"
  where "pupr_le a b = (Rep_pupr a = Rep_pupr b \<or> (Rep_pupr a = ''public''))"

definition pupr_less :: "pupr \<Rightarrow> pupr \<Rightarrow> bool"
  where "pupr_less a b = ((Rep_pupr a = ''public'') \<and> (Rep_pupr b = ''private''))"

instantiation "pupr" :: linorder
begin
definition
  pupr_le_inst: \<open>(a \<le> b) = (pupr_le a b)\<close>
definition 
  pupr_less: \<open>(a < b) = (pupr_less a b)\<close>

instance 
  apply (rule Orderings.linorder.intro_of_class)
  thm Orderings.class.linorder_def
  apply (simp add: Orderings.class.linorder_def)
  apply (rule conjI)
   prefer 2
  apply (simp add: Orderings.class.linorder_axioms_def)
   apply (smt (verit) Rep_pupr empty_iff insert_iff pupr_le_def pupr_le_inst)
  apply (simp add: Orderings.class.order_def)
  apply (simp add: Orderings.class.order_axioms_def)
  apply (rule conjI)
  prefer 2
  apply (metis Rep_pupr_inject pupr_le_def pupr_le_inst)
  apply (simp add: Orderings.class.preorder_def)
  using Rep_pupr pupr_le_def pupr_le_inst pupr_less pupr_less_def by auto
end


(* Second part of the MLS example inspired by Gollmann (but with airplane actors instead
   PER ENG ) *)
typedef airplane_actors = "{S. S \<subseteq> {''Alice'', ''Bob'', ''Charly''}}"
  by blast

definition 
  le_aa: \<open>le_aa a b = (Rep_airplane_actors a \<subseteq> Rep_airplane_actors b)\<close>
definition 
  less_aa: \<open>less_aa a b = (Rep_airplane_actors a \<subset> Rep_airplane_actors b)\<close>
definition 
  inf_aa : \<open>inf_aa a b = Abs_airplane_actors(Rep_airplane_actors a \<inter> Rep_airplane_actors b)\<close>
definition
  sup_aa :\<open>sup_aa a b = Abs_airplane_actors(Rep_airplane_actors a \<union> Rep_airplane_actors b)\<close>

lemma inf_less_l: \<open>le_aa (inf_aa a b) a\<close>
  by (smt (verit) Abs_airplane_actors_inverse Int_subset_iff Rep_airplane_actors dual_order.trans equalityD1 inf_aa le_aa mem_Collect_eq)

lemma inf_less_r: \<open>le_aa (inf_aa a b) b\<close>
  by (metis inf_aa inf_commute inf_less_l)


instantiation "airplane_actors" :: lattice
begin
definition 
  inf_aa_inst: \<open>inf a b = inf_aa a b\<close>
definition
  sup_aa_inst: \<open>sup a b = sup_aa a b\<close>
definition 
  le_aa_inst: \<open>a \<le> b = le_aa a b\<close>
definition 
  less_aa_inst: \<open>a < b = less_aa a b\<close>

instance 
  apply (rule Lattices.lattice.intro_of_class)
  apply (simp add: Lattices.class.lattice_def)
  apply (rule conjI)
   apply (simp add: Lattices.class.semilattice_inf_def)
  apply (rule conjI)
  apply (simp add: Orderings.class.order_def)
  apply (rule conjI)
     apply (simp add: Orderings.class.preorder_def)
  using le_aa le_aa_inst less_aa less_aa_inst apply auto[1]
  apply (simp add: Orderings.class.order_axioms_def)
    apply (simp add: Rep_airplane_actors_inject le_aa le_aa_inst)
   apply (simp add: Lattices.class.semilattice_inf_axioms_def)
  apply (intro conjI)
     apply (simp add: inf_aa_inst inf_less_l le_aa_inst)
    apply (simp add: inf_aa_inst inf_less_r le_aa_inst)
  apply (smt (verit, ccfv_threshold) Abs_airplane_actors_inverse Rep_airplane_actors inf.absorb_iff2 inf_aa inf_aa_inst inf_assoc le_aa le_aa_inst mem_Collect_eq)
   apply (simp add: Lattices.class.semilattice_sup_def)
  apply (rule conjI)
  apply (simp add: Orderings.class.order_def)
  apply (simp add: Orderings.class.order_axioms_def)
  apply (rule conjI)
  apply (simp add: Orderings.class.preorder_def)
  using le_aa le_aa_inst less_aa less_aa_inst apply fastforce
   apply (simp add: Rep_airplane_actors_inject le_aa le_aa_inst)
   apply (simp add: Lattices.class.semilattice_sup_axioms_def)
  using Abs_airplane_actors_inverse Rep_airplane_actors le_aa le_aa_inst sup_aa sup_aa_inst by auto


(* It is surprisingly complicated to instantiate simple finite orders into the
   classes linord and lattice. But with these preparations we are able to 
   apply the MLS order to an example. Showing that the two order pupr_le
   and le_aa defined above can now be plugged into the MLS_ord definition
   (as indices of the \<preceq>) and that we can then unfold the definition of
   MLS_ord (and the typedefs of the two used orders) to show that two 
   security classes are in the MLS order relation. 
   The example shows (public, {Alice}) \<preceq> (private, {Alice,Bob}.
 *)
lemma MLS_ex: \<open>(Abs_pupr ''public'', Abs_airplane_actors({''Alice''}))
               \<preceq>\<^sub>(pupr_le,le_aa)
               (Abs_pupr ''private'', Abs_airplane_actors({''Alice'', ''Bob''}))\<close>
  apply (simp add: MLS_order_def pupr_le_def le_aa)
  by (simp add: Abs_airplane_actors_inverse Abs_pupr_inverse)

(* However, to apply this to infrastructure systems it might 
   well be worth considering to use the Decentralized Label Model 
   that emphasizes also ownership of objects. We will next show how this can 
   be formalized but in a more lightweight fashion because the label sets of
   sets of actors may vary.  *)

end
end