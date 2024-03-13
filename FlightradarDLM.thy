theory FlightradarDLM
  imports IFC
begin
datatype action = move | display

type_synonym actor = "string"
type_synonym identity = string
type_synonym policy = "((actor => bool) * action set)"
type_synonym data = "string"

datatype location = Location nat
primrec lSuc where "lSuc (Location l) = Location (Suc l)"
primrec lPred where "lPred (Location l) = Location (l - 1)"

datatype igraph = Lgraph (gra: "(location \<times> location)set")
                         (flights:  "location \<times> location \<Rightarrow> identity set")
                         (passengers: "identity \<Rightarrow> actor set")
                         (routes: "identity \<Rightarrow> (location \<times> location)list")
                         (critact: "actor \<Rightarrow> bool")
                         (critloc: "location \<times> location \<Rightarrow> bool")
                         (critpos: "identity \<Rightarrow> (location \<times> location)option")

datatype infrastructure =
         Infrastructure (graphI: "igraph")
                        (policI: "location \<times> location \<Rightarrow> policy set")

definition airplanes_graph :: "igraph \<Rightarrow> identity set"  
  where  "airplanes_graph g == {x. ? y. y : gra g \<and> x \<in> (flights g y)}"

definition atI :: "[identity, igraph, location \<times> location] \<Rightarrow> bool" ("_ @\<^bsub>(_)\<^esub> _" 50)
where "a @\<^bsub>G\<^esub> l \<equiv> a \<in> (flights G l)"

definition enables :: "[infrastructure, location \<times> location, actor, action] \<Rightarrow> bool"
where
"enables I ll' h a \<equiv>  (\<exists> (p,e) \<in> policI I ll'. a \<in> e \<and> p h)"

fun circumvent
  where   
"circumvent (l,l')(n,n') = (if l = n then (lSuc l, n') else (n,lSuc n'))"

fun vicinity 
  where
"vicinity (c,c') = {(lPred c,c'),(lSuc c,c'),(c,lPred c),(c,lSuc c'),
                    (lPred c,lPred c'),(lSuc c,lSuc c'),(lPred c,lSuc c'),(lSuc c,lSuc c')}"

(* The move crit case effectively moves the plane forward as in the move case but
   in addition the real circumvented position is registered in critpos. Compared
   to an earlier version (also still in the submitted paper) this makes blurring
   much easier: in fact one only has to additionally hide the critpos component. *)
inductive state_transition_in :: "[infrastructure, infrastructure] \<Rightarrow> bool" ("(_ \<rightarrow>\<^sub>n _)" 50)
where
move: "G = graphI I \<Longrightarrow> (l, l') \<in> gra G \<Longrightarrow> f \<in> flights G (l, l') \<Longrightarrow>
      (n,n') = hd(routes G f) \<Longrightarrow> \<not>(critloc G (n, n')) \<Longrightarrow>
      I' = Infrastructure 
          (Lgraph (gra G) 
                  (((flights G)((l,l') := (flights G (l,l')) - {f}))
                               ((n,n') := (flights G (n,n')) \<union> {f}))
                  (passengers G)
                  ((routes G)(f := tl(routes G f)))
                  (critact G)
                  (critloc G)
                  ((critpos G)(f := None)))
            (policI I)
       \<Longrightarrow> I \<rightarrow>\<^sub>n I'" |
move_crit: "G = graphI I \<Longrightarrow> (l, l') \<in> gra G \<Longrightarrow> f \<in> flights G (l, l') \<Longrightarrow>
      (n,n') = hd(routes G f) \<Longrightarrow> critloc G (n, n') \<Longrightarrow>
      I' = Infrastructure 
          (Lgraph (gra G) 
                  (((flights G)((l,l') := (flights G (l,l')) - {f}))
                               ((n,n') := (flights G (n,n')) \<union> {f}))
                  (passengers G)
                  ((routes G)(f := tl(routes G f)))
                  (critact G)
                  (critloc G)
                  ((critpos G)(f := Some(circumvent (l,l')(n,n')))))
            (policI I)
       \<Longrightarrow> I \<rightarrow>\<^sub>n I'" 


(* A functon "blur" achieves hiding the security critical components from outsiders
   - here Eve - who aren't in the aircontrollers group. For simplicity, we use 
   a function that deletes these security critical components rather than
   parametrizing the indist. definition by security classes. *)
(* It is a bit simplistic to just delete the "high-security" components
  in order to hide them. In a refined version, we will use the MLS lattices
  from IFC.thy. Thereby we can give a more general definition of indistinguishability 
  in which the variables that are now simply "blurred away" are not visible, that is,
  not relevant for indistinguishability. However, it will turn out that the practical
  version of indistinguishability using blur is equivalent (albeit less general). 
  That is, it suffices to prove noninterference. *)
definition blur
  where
\<open>blur I =  Infrastructure
            (Lgraph
              (gra (graphI I))
              (flights(graphI I))
              (passengers (graphI I))
              (routes (graphI I))
              (\<lambda> x. True)
              (\<lambda> x. True)
              (\<lambda> x. None))
           (policI I)\<close>

(* This definition is used in the paper. We now use the above one as it is simpler
   and easier to use.*)
definition blur'
  where
\<open>blur' I =  Infrastructure
            (Lgraph
              (gra (graphI I))
              (\<lambda> (l,l'). if critloc(graphI I)(l,l') then
                   flights(graphI I)(l,l') \<union> \<Union> (flights(graphI I)`(vicinity (l,l')))
                  else flights(graphI I)(l,l'))
                  (passengers (graphI I))
                  (routes (graphI I))
                  (\<lambda> x. True)
                  (\<lambda> x. True)
                  (\<lambda> x. None))
           (policI I)\<close>


(* show that this infrastructure is a state as given in MC.thy *)
instantiation "infrastructure" :: state
begin

definition 
   state_transition_infra_def: "(i \<rightarrow>\<^sub>i i') =  (i \<rightarrow>\<^sub>n (i' :: infrastructure))"

instance
  by (rule MC.state.intro_of_class)

definition state_transition_in_refl ("(_ \<rightarrow>\<^sub>n* _)" 50)
where "s \<rightarrow>\<^sub>n* s' \<equiv> ((s,s') \<in> {(x,y). state_transition_in x y}\<^sup>*)"
  
end


definition aircontrollers
  where
\<open>aircontrollers = {''Alice'', ''Bob'', ''Charly''}\<close>


definition indistinguishability ("(_ \<sim>\<^sub>_ _)" 50)
  where "s0 \<sim>\<^sub>h s1 = (if h \<in> aircontrollers then (s0 = s1) else (blur s0 = blur s1))"

lemma gra_inv: \<open>s0 \<rightarrow>\<^sub>n s0' \<Longrightarrow> gra (graphI s0) = gra (graphI s0')\<close>
  apply (erule state_transition_in.cases)
  using igraph.sel(1) infrastructure.sel(1) apply presburger
  using igraph.sel(1) infrastructure.sel(1) by presburger

theorem noninterference:
\<open>(\<forall> s0 s1 s0'. (s0 \<sim>\<^sub>''Eve'' s1) \<longrightarrow> (s0 \<rightarrow>\<^sub>n s0') \<longrightarrow> (\<exists> s1'. (s1 \<rightarrow>\<^sub>n* s1') \<and> (s0' \<sim>\<^sub>''Eve'' s1')))\<close> 
  apply (unfold indistinguishability_def aircontrollers_def)
  apply (simp add: blur_def state_transition_in_refl_def)
  apply auto
  apply (erule state_transition_in.cases)
(* First case \<not> critloc (graphI I) (n, n')*)
(* Again need to make case analysis over critloc (graphI s1)(n, n')
   as critloc is blurred! *)
   apply (case_tac "critloc (graphI s1) (n, n')")
    prefer 2
(* \<not> critloc (graphI s1) (hd (routes (graphI s1) f)) *)
  apply (rule_tac x = \<open>Infrastructure
        (Lgraph (gra (graphI s1))
          ((flights(graphI s1))((l, l'):= flights (graphI s1) (l, l') - {f}, (n, n') := flights (graphI s1) (n, n') \<union> {f}))
          (passengers (graphI s1)) ((routes (graphI s1))
           (f := tl (routes (graphI s1) f))) (critact (graphI s1)) (critloc (graphI s1))
          ((critpos (graphI s1))(f := None)))(policI s1)\<close> in exI)
   apply (intro conjI)
  prefer 2
        apply force
  prefer 2
       apply force
      prefer 2
      apply force
  prefer 2
     apply force
    prefer 2
    apply force
  apply (subgoal_tac \<open>(s1,
        Infrastructure
         (Lgraph (gra (graphI s1))
           ((flights (graphI s1))
            ((l, l') := flights (graphI s1) (l, l') - {f},
             (n, n') := flights (graphI s1) (n, n') \<union> {f}))
           (passengers (graphI s1)) ((routes (graphI s1))(f := tl (routes (graphI s1) f)))
           (critact (graphI s1)) (critloc (graphI s1)) ((critpos (graphI s1))(f := None)))
         (policI s1))
       \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<close>)
    apply force
   apply simp
   apply (rule state_transition_in.move)
        apply (rule refl)
        apply (assumption)+
     apply simp
  apply simp
(* critloc (graphI s1) (hd (routes (graphI s1) f)) *)
apply (rule_tac x = \<open>Infrastructure 
          (Lgraph (gra (graphI s1)) 
                  (((flights (graphI s1))((l,l') := (flights (graphI s1) (l,l')) - {f}))
                               ((n,n') := (flights (graphI s1) (n,n')) \<union> {f}))
                  (passengers (graphI s1))
                  ((routes (graphI s1))(f := tl(routes (graphI s1) f)))
                  (critact (graphI s1))
                  (critloc (graphI s1))
                  ((critpos (graphI s1))(f := Some(circumvent (l,l')(n,n')))))
            (policI I)\<close> in exI)
   apply (intro conjI)
  apply (subgoal_tac \<open>(s1,
        Infrastructure
         (Lgraph (gra (graphI s1))
           ((flights (graphI s1))
            ((l, l') := flights (graphI s1) (l, l') - {f},
             (n, n') := flights (graphI s1) (n, n') \<union> {f}))
           (passengers (graphI s1)) ((routes (graphI s1))(f := tl (routes (graphI s1) f)))
           (critact (graphI s1)) (critloc (graphI s1))
           ((critpos (graphI s1))(f \<mapsto> circumvent (l, l') (n, n'))))
         (policI I))
       \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<close>)
         apply force
        apply simp
   apply (rule state_transition_in.move_crit)
        apply (rule refl)
        apply (assumption)+
         apply simp
  apply simp+
(* Second case: critloc (graphI I) (n, n')*)
   apply (case_tac "critloc (graphI s1) (n, n')")
apply (rule_tac x = \<open>Infrastructure 
          (Lgraph (gra (graphI s1)) 
                  (((flights (graphI s1))((l,l') := (flights (graphI s1) (l,l')) - {f}))
                               ((n,n') := (flights (graphI s1) (n,n')) \<union> {f}))
                  (passengers (graphI s1))
                  ((routes (graphI s1))(f := tl(routes (graphI s1) f)))
                  (critact (graphI s1))
                  (critloc (graphI s1))
                  ((critpos (graphI s1))(f := Some(circumvent (l,l')(n,n')))))
            (policI I)\<close> in exI)
   apply (intro conjI)
  apply (subgoal_tac \<open>(s1,
        Infrastructure
         (Lgraph (gra (graphI s1))
           ((flights (graphI s1))
            ((l, l') := flights (graphI s1) (l, l') - {f},
             (n, n') := flights (graphI s1) (n, n') \<union> {f}))
           (passengers (graphI s1)) ((routes (graphI s1))(f := tl (routes (graphI s1) f)))
           (critact (graphI s1)) (critloc (graphI s1))
           ((critpos (graphI s1))(f \<mapsto> circumvent (l, l') (n, n'))))
         (policI I))
       \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<close>)
         apply force
        apply simp
   apply (rule state_transition_in.move_crit)
        apply (rule refl)
        apply (assumption)+
         apply simp
  apply simp+
(* Second case - second case:  \<not> critloc (graphI s1) (hd (routes (graphI s1) f)) *)
  apply (rule_tac x = \<open>Infrastructure
        (Lgraph (gra (graphI s1))
          ((flights(graphI s1))((l, l'):= flights (graphI s1) (l, l') - {f}, (n, n') := flights (graphI s1) (n, n') \<union> {f}))
          (passengers (graphI s1)) ((routes (graphI s1))
           (f := tl (routes (graphI s1) f))) (critact (graphI s1)) (critloc (graphI s1))
          ((critpos (graphI s1))(f := None)))(policI s1)\<close> in exI)
  apply (subgoal_tac \<open>(s1,
        Infrastructure
         (Lgraph (gra (graphI s1))
           ((flights (graphI s1))
            ((l, l') := flights (graphI s1) (l, l') - {f},
             (n, n') := flights (graphI s1) (n, n') \<union> {f}))
           (passengers (graphI s1)) ((routes (graphI s1))(f := tl (routes (graphI s1) f)))
           (critact (graphI s1)) (critloc (graphI s1)) ((critpos (graphI s1))(f := None)))
         (policI s1))
       \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<close>)
    apply force
   apply simp
   apply (rule state_transition_in.move)
        apply (rule refl)
        apply (assumption)+
     apply simp
 by simp


end
