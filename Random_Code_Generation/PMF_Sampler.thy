theory PMF_Sampler
  imports "HOL-Probability.Probability" "HOL-Library.Code_Lazy" Prereqs Prefix_Tree
begin

lemma measurable_sets_space_UNIV:
  "f \<in> M \<rightarrow>\<^sub>M N \<Longrightarrow> space M = UNIV \<Longrightarrow> X \<in> sets N \<Longrightarrow> f -` X \<in> sets M"
  using measurable_sets[of f M N X] by simp

lemma measurable_sets_coin_space:
  "f \<in> coin_space \<rightarrow>\<^sub>M N \<Longrightarrow> X \<in> sets N \<Longrightarrow> f -` X \<in> sets coin_space"
  by (erule measurable_sets_space_UNIV) (simp_all add: space_coin_space)

lemma measurable_stake_coin_space [measurable]:
   "coin_space.random_variable (count_space UNIV) (stake n)"
  by (simp add: coin_space_def)

lemma measurable_sdrop_coin_space [measurable]:
   "coin_space.random_variable coin_space (sdrop n)"
  by (simp add: coin_space_def)

lemma UNIV_in_sets_coin_space [measurable, simp]: "UNIV \<in> sets coin_space"
  by (metis sets.top space_coin_space)

lemma emeasure_coin_space:
  assumes "X \<in> sets coin_space"
  shows   "emeasure coin_space X =
             (emeasure coin_space {x. True ## x \<in> X} +
              emeasure coin_space {x. False ## x \<in> X}) / 2"
  unfolding coin_space_def
proof (subst prob_space.emeasure_stream_space; (fold coin_space_def)?)
  show "prob_space (measure_pmf (pmf_of_set (UNIV :: bool set)))"
    by (simp add: measure_pmf.prob_space_axioms)
  show "X \<in> sets coin_space"
    by fact
  show "(\<integral>\<^sup>+ t. emeasure coin_space {x \<in> space coin_space. t ## x \<in> X}
           \<partial>measure_pmf (pmf_of_set UNIV)) =
          (emeasure coin_space {x. True ## x \<in> X} +
           emeasure coin_space {x. False ## x \<in> X}) / 2"
    by (subst nn_integral_measure_pmf, subst nn_integral_count_space_finite)
       (auto simp: UNIV_bool divide_ennreal_def algebra_simps space_coin_space)
qed

lemma emeasure_coin_space_stake_sdrop:
  assumes "\<And>xs. xs \<in> A \<Longrightarrow> length xs = n"
  assumes "B \<in> sets coin_space"
  shows   "emeasure coin_space {bs. stake n bs \<in> A \<and> sdrop n bs \<in> B} =
             card A / 2 ^ n * emeasure coin_space B"
  using assms
proof (induction n arbitrary: A)
  case 0
  from 0 have "A \<in> {{}, {[]}}"
    by auto
  thus ?case by auto
next
  case (Suc n)
  define P where "P = (\<lambda>X. emeasure coin_space X)"
  define AT where "AT = (\<lambda>xs. True # xs) -` A"
  define AF where "AF = (\<lambda>xs. False # xs) -` A"
  have fin: "finite A"
    by (rule finite_subset[OF _ finite_lists_length_eq[of UNIV "Suc n"]])
       (use Suc.prems in auto)

  have "P {bs. stake (Suc n) bs \<in> A \<and> sdrop (Suc n) bs \<in> B} =
          (P {x. True # stake n x \<in> A \<and> sdrop n x \<in> B} +
           P {x. False # stake n x \<in> A \<and> sdrop n x \<in> B}) / 2"
    unfolding P_def
  proof (subst emeasure_coin_space)
    have "{bs. stake (Suc n) bs \<in> A \<and> sdrop (Suc n) bs \<in> B} = 
            stake (Suc n) -` A \<inter> sdrop (Suc n) -` B"
      by auto
    also have "\<dots> \<in> coin_space.events"
      by (rule sets.Int measurable_sets_coin_space measurable_stake_coin_space
               sets_UNIV measurable_sdrop_coin_space Suc.prems)+
    finally show "{bs. stake (Suc n) bs \<in> A \<and> sdrop (Suc n) bs \<in> B} \<in> coin_space.events" .
  qed simp_all
  also have "{x. True # stake n x \<in> A \<and> sdrop n x \<in> B} = {x. stake n x \<in> AT \<and> sdrop n x \<in> B}"
    by (auto simp: AT_def)
  also have "{x. False # stake n x \<in> A \<and> sdrop n x \<in> B} = {x. stake n x \<in> AF \<and> sdrop n x \<in> B}"
    by (auto simp: AF_def)
  also have "P {x. stake n x \<in> AT \<and> sdrop n x \<in> B} =
             ennreal (real (card AT) / 2 ^ n) * emeasure coin_space B"
    unfolding P_def using Suc.prems by (intro Suc.IH) (force simp: AT_def)
  also have "P {x. stake n x \<in> AF \<and> sdrop n x \<in> B} =
             ennreal (real (card AF) / 2 ^ n) * emeasure coin_space B"
    unfolding P_def using Suc.prems by (intro Suc.IH) (force simp: AF_def)
  also have "(ennreal (real (card AT) / 2 ^ n) * emeasure coin_space B +
              ennreal (real (card AF) / 2 ^ n) * emeasure coin_space B) / 2 =
             (ennreal (real (card AT + card AF))) * emeasure coin_space B / 2 ^ Suc n"
    by (simp add: divide_ennreal_def algebra_simps ennreal_inverse_mult power_less_top_ennreal 
             flip: divide_ennreal ennreal_power)
  also have "card AT = card ((\<lambda>xs. True # xs) ` AT)"
    by (subst card_image) (auto simp: inj_on_def)
  also have "card AF = card ((\<lambda>xs. False # xs) ` AF)"
    by (subst card_image) (auto simp: inj_on_def)
  also have "card ((\<lambda>xs. True # xs) ` AT) + card ((\<lambda>xs. False # xs) ` AF) =
             card ((\<lambda>xs. True # xs) ` AT \<union> (\<lambda>xs. False # xs) ` AF)"
    using fin by (intro card_Un_disjoint [symmetric]) (auto simp: AT_def AF_def)
  also have "(\<lambda>xs. True # xs) ` AT \<union> (\<lambda>xs. False # xs) ` AF = A"
  proof (intro equalityI subsetI)
    fix xs assume xs: "xs \<in> A"
    with Suc.prems have "length xs = Suc n"
      by auto
    with xs show "xs \<in> (\<lambda>xs. True # xs) ` AT \<union> (\<lambda>xs. False # xs) ` AF"
      using Suc.prems by (cases xs) (auto simp: AT_def AF_def)
  qed (auto simp: AT_def AF_def)
  finally show ?case 
    by (simp add: divide_ennreal_def algebra_simps ennreal_inverse_mult power_less_top_ennreal 
                  P_def ennreal_mult flip: divide_ennreal ennreal_power)
qed

lemma emeasure_coin_space_stake:
  assumes "\<And>xs. xs \<in> A \<Longrightarrow> length xs = n"
  shows   "emeasure coin_space (stake n -` A) = card A / 2 ^ n"
  using emeasure_coin_space_stake_sdrop[of A n UNIV] assms by (simp add: vimage_def)



lifting_forget ptree.lifting

type_synonym 'a pmfsr = "bool stream \<Rightarrow> ('a \<times> nat) option"

definition wf_pmfsr :: "'a pmfsr \<Rightarrow> bool" where
  "wf_pmfsr p \<longleftrightarrow>
     (\<forall>bs. case p bs of None \<Rightarrow> True | Some (x, n) \<Rightarrow>
       (\<forall>bs'. stake n bs' = stake n bs \<longrightarrow> p bs' = p bs))"

lemma wf_pmfsr_const_None [simp, intro]: "wf_pmfsr (\<lambda>_. None)"
  by (auto simp: wf_pmfsr_def)

lemma wf_pmfsrI:
  assumes "\<And>bs bs' x n. r bs = Some (x, n) \<Longrightarrow> stake n bs' = stake n bs \<Longrightarrow> r bs' = Some (x, n)"
  shows "wf_pmfsr r"
  unfolding wf_pmfsr_def 
proof
  fix bs :: "bool stream"
  show "case r bs of None \<Rightarrow> True
          | Some (xa, n) \<Rightarrow> \<forall>bs'. stake n bs' = stake n bs \<longrightarrow> r bs' = r bs"
  proof (cases "r bs")
    case (Some xn)
    thus ?thesis
      using assms[of bs "fst xn" "snd xn"] by auto
  qed auto
qed
    

lemma wf_pmfsrD:
  assumes "wf_pmfsr r" "r bs = Some (x, n)" "stake n bs' = stake n bs"
  shows   "r bs' = Some (x, n)"
proof -
  have "(case r bs of None \<Rightarrow> True
         | Some (xa, n) \<Rightarrow> \<forall>bs'. stake n bs' = stake n bs \<longrightarrow> r bs' = r bs)"
    using assms(1) unfolding wf_pmfsr_def by blast
  thus ?thesis using assms(2-)
    by auto
qed


typedef 'a sampler = "{p :: 'a pmfsr. wf_pmfsr p}"
  by (rule exI[of _ "\<lambda>_. None"]) (auto simp: wf_pmfsr_def)

setup_lifting type_definition_sampler

lift_definition run_sampler :: "'a sampler \<Rightarrow> bool stream \<Rightarrow> ('a \<times> nat) option"
  is "\<lambda>p. p" .

lift_definition sampler_of_ptree :: "bool ptree \<Rightarrow> bool list sampler" is
  "\<lambda>(t :: bool ptree) (bs :: bool stream). map_option (\<lambda>bs'. (bs', length bs')) (prefix_of_ptree t bs)"
  apply (auto simp: wf_pmfsr_def split: option.splits)
  apply (simp add: prefix_of_ptree_eq_Some_iff sprefix_def)
  done

lift_definition return_sampler :: "'a \<Rightarrow> 'a sampler" is "\<lambda>x bs. Some (x, 0)"
  by (auto simp: wf_pmfsr_def)

lift_definition singleton_sampler :: "bool list \<Rightarrow> bool list sampler" is
  "\<lambda>bs' bs. if sprefix bs' bs then Some (bs', length bs') else None"
  by (auto simp: wf_pmfsr_def sprefix_def)

lift_definition map_sampler :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a sampler \<Rightarrow> 'b sampler" is
  "\<lambda>f r bs. map_option (map_prod f id) (r bs)"
  apply (rule wf_pmfsrI)
  apply (auto)
  using wf_pmfsrD
  apply fast
  done


setup_lifting type_definition_ptree

lift_definition ptree_of_sampler :: "'a sampler \<Rightarrow> bool ptree" is
  "\<lambda>p. {bs. \<exists>x. p (bs @- sconst False) = Some (x, length bs)}"
  apply (rule pairwiseI)
  apply (auto)
  using wf_pmfsrD
  by (smt (verit, ccfv_SIG) option.inject parallel_def prefix_def prod.inject
           shift_append sprefix_def sprefix_shift_same)

lemma set_ptree_of_sampler:
  "set_ptree (ptree_of_sampler p) =
     {bs. \<exists>x. run_sampler p (bs @- sconst False) = Some (x, length bs)}"
  by transfer auto




lemma sampler_eqI: "(\<And>bs. run_sampler p bs = run_sampler q bs) \<Longrightarrow> p = q"
  by transfer auto

lemma singleton_sampler_Nil [simp]: "singleton_sampler [] = return_sampler []"
  by transfer (auto simp: sprefix_def)

lemma run_sampler_return [simp]:
  "run_sampler (return_sampler x) bs = Some (x, 0)"
  by transfer auto

lemma run_sampler_singleton:
  "run_sampler (singleton_sampler bs') bs =
     (if sprefix bs' bs then Some (bs', length bs') else None)"
  by transfer auto

lemma run_sampler_singleton' [simp]:
  "sprefix bs' bs \<Longrightarrow> run_sampler (singleton_sampler bs') bs = Some (bs', length bs')"
  "\<not>sprefix bs' bs \<Longrightarrow> run_sampler (singleton_sampler bs') bs = None"
  by (auto simp: run_sampler_singleton)

lemma run_sampler_map [simp]:
  "run_sampler (map_sampler f p) = map_option (map_prod f id) \<circ> run_sampler p"
  by transfer auto

lemma run_sampler_of_ptree:
  "run_sampler (sampler_of_ptree t) =
     map_option (\<lambda>bs'. (bs', length bs')) \<circ> prefix_of_ptree t"
  by transfer auto

lemma sampler_of_ptree_singleton [simp]:
  "sampler_of_ptree (singleton_ptree bs) = singleton_sampler bs"
  by (rule sampler_eqI) (auto simp: run_sampler_of_ptree prefix_of_ptree_singleton)

lemma ptree_of_sampler_of_ptree [simp]:
  "ptree_of_sampler (sampler_of_ptree t) = t"
  by (subst ptree.set_ptree_inject [symmetric])
     (auto simp: set_ptree_of_sampler run_sampler_of_ptree 
                 prefix_of_ptree_simps sprefix_def)

lemma ptree_of_sampler_return [simp]:
  "ptree_of_sampler (return_sampler x) = ptree_of_length 0"
  by (subst ptree.set_ptree_inject [symmetric])
     (auto simp: set_ptree_of_sampler)

lemma ptree_of_sampler_map [simp]:
  "ptree_of_sampler (map_sampler f p) = ptree_of_sampler p"
  by transfer auto


lemma run_sampler_prefix:
  assumes "run_sampler p bs = Some (x, n)" "stake n bs = stake n bs'"
  shows   "run_sampler p bs' = Some (x, n)"
  using assms
  apply transfer
  using wf_pmfsrD
  apply metis
  done

lift_definition fun_sampler :: "'a sampler \<Rightarrow> bool list \<Rightarrow> 'a" is
  "\<lambda>p bs. fst (the (p (bs @- sconst False)))" .

lemma fun_sampler_altdef:
  "fun_sampler p = (\<lambda>bs. fst (the (run_sampler p (bs @- sconst False))))"
  by transfer auto


lemma sampler_decompose:
  fixes p :: "'a sampler"
  defines "f \<equiv> fun_sampler p"
  defines "t \<equiv> ptree_of_sampler p"
  shows   "p = map_sampler f (sampler_of_ptree t)"
proof (rule sampler_eqI)
  fix bs :: "bool stream"
  have "run_sampler (map_sampler f (sampler_of_ptree t)) bs =
          map_option (\<lambda>x. (f x, length x)) (prefix_of_ptree t bs)"
    by (simp add: run_sampler_of_ptree option.map_comp o_def)
  also have "\<dots> = run_sampler p bs"
  proof (cases "run_sampler p bs")
    case None
    thus ?thesis
      apply (auto simp: prefix_of_ptree_eq_None_iff sprefix_def t_def set_ptree_of_sampler)
      using run_sampler_prefix apply fastforce
      done
  next
    case (Some xn)
    obtain x n where [simp]: "xn = (x, n)"
      by (cases xn)
    define bs' where "bs' = stake n bs"
    have *: "run_sampler p (bs' @- sconst False) = Some (x, n)"
      by (rule run_sampler_prefix[where bs = bs]) (use Some in \<open>auto simp: bs'_def\<close>)
    hence "prefix_of_ptree (ptree_of_sampler p) bs = Some bs'"
      by (intro prefix_of_ptree_eq_SomeI)
         (auto simp: sprefix_def bs'_def t_def set_ptree_of_sampler)
    thus ?thesis
      using Some * by (auto simp: bs'_def t_def f_def fun_sampler_altdef)
  qed
  finally show "run_sampler p bs =
                run_sampler (map_sampler f (sampler_of_ptree t)) bs" ..
qed

lemma sampler_cases[cases type]:
  fixes p :: "'a sampler"
  obtains f t where  "p = map_sampler f (sampler_of_ptree t)"
  using sampler_decompose[of p] by blast

lift_definition bind_sampler :: "'a sampler \<Rightarrow> ('a \<Rightarrow> 'b sampler) \<Rightarrow> 'b sampler" is
  "\<lambda>p q bs.
    do {(x, m) \<leftarrow> p bs;
        (y, n) \<leftarrow> q x (sdrop m bs);
        Some (y, m + n)}"
proof -
  fix p :: "'a pmfsr" and q :: "'a \<Rightarrow> 'b pmfsr"
  assume p: "wf_pmfsr p" and q: "\<And>x. wf_pmfsr (q x)"
  show "wf_pmfsr (\<lambda>bs. p bs \<bind>
          (\<lambda>(x, m). q x (sdrop m bs) \<bind> (\<lambda>(y, n). Some (y, m + n))))"
  proof (rule wf_pmfsrI, goal_cases)
    case (1 bs bs' y n)
    then obtain n1 n2 x where 2:
      "p bs = Some (x, n1)" "q x (sdrop n1 bs) = Some (y, n2)" "n = n1 + n2"
      by (auto simp: Option_bind_conv_case split: option.splits)
    have "stake n1 bs' = stake n1 bs"
      using 1(2) 2(3) by (metis le_add1 min_def_raw take_stake)
    from p and 2(1) and this have 3: "p bs' = Some (x, n1)"
      by (rule wf_pmfsrD)
    have "stake n2 (sdrop n1 bs') = stake n2 (sdrop n1 bs)"
      using 1(2) 2(3) by (metis diff_add_inverse drop_stake)
    hence 4: "q x (sdrop n1 bs') = Some (y, n2)"
      by (rule wf_pmfsrD[OF q 2(2)])
    show ?case
      using 1(2) 2 3 4 by auto
  qed
qed

adhoc_overloading Monad_Syntax.bind bind_sampler


lemma bind_assoc_sampler: "(p :: 'a sampler) \<bind> q \<bind> r = p \<bind> (\<lambda>x. q x \<bind> r)"
  by transfer (auto simp: Option_bind_conv_case split: option.splits)

lemma bind_map_sampler:
  "bind_sampler (map_sampler f p) q = bind_sampler p (q \<circ> f)"
  by transfer (auto simp: fun_eq_iff Option_bind_conv_case split: option.splits)

lemma run_sampler_bind:
  fixes p :: "'a sampler"
  shows "run_sampler (p \<bind> q) bs =
            do {(x, m) \<leftarrow> run_sampler p bs;
                (y, n) \<leftarrow> run_sampler (q x) (sdrop m bs);
                Some (y, m + n)}"
  by transfer simp

lemma map_bind_sampler:
  "map_sampler f (bind_sampler p q) = bind_sampler p (\<lambda>x. map_sampler f (q x))"
  by (rule sampler_eqI)
     (auto simp: run_sampler_bind Option_bind_conv_case split: option.splits)

lemma bind_return_sampler: "return_sampler x \<bind> f = f x"
  by transfer auto

lemma bind_return_sampler': "p \<bind> return_sampler = p"
  by transfer auto

lemma map_conv_bind_sampler: "map_sampler f p = bind_sampler p (\<lambda>x. return_sampler (f x))"
  by transfer (auto simp: Option_bind_conv_case split: option.splits)

lemma map_return_sampler [simp]: "map_sampler f (return_sampler x) = return_sampler (f x)"
  by transfer auto

lemma map_map_sampler: "map_sampler f (map_sampler g p) = map_sampler (f \<circ> g) p"
  by transfer (auto simp: option.map_comp o_def prod.map_comp id_def)
 
lemma bind_sampler_decompose:
  "map_sampler f (sampler_of_ptree t1) \<bind> (\<lambda>x. map_sampler (g x) (sampler_of_ptree t2)) =
   map_sampler (\<lambda>(x,y). g (f x) y)
     (do {bs \<leftarrow> sampler_of_ptree t1; bs' \<leftarrow> sampler_of_ptree t2; return_sampler (bs, bs')})"
  by (simp add: map_bind_sampler bind_assoc_sampler bind_map_sampler o_def map_map_sampler
           flip: map_conv_bind_sampler)

lemma ord_option_case:
  "ord_option le x y \<longleftrightarrow>
     (case x of None \<Rightarrow> True | Some x' \<Rightarrow> (case y of None \<Rightarrow> False | Some y' \<Rightarrow> le x' y'))"
  by (auto split: option.splits)




definition ord_pmfsr :: "'a pmfsr \<Rightarrow> 'a pmfsr \<Rightarrow> bool" where
  "ord_pmfsr = rel_fun (=) (ord_option (=))"

lemma ord_pmfsrD: "ord_pmfsr r s \<Longrightarrow> r bs = Some xn \<Longrightarrow> s bs = Some xn"
  unfolding ord_pmfsr_def rel_fun_def
  by (metis ord_option_eq_simps(2))

context fixes Y :: "'a pmfsr set" begin

definition lub_pmfsr :: "'a pmfsr" where
  "lub_pmfsr bs = 
     (let X = {xn |xn r. r \<in> Y \<and> r bs = Some xn}
      in  if Set.is_singleton X then Some (the_elem X) else None)"

lemma lub_pmfsr_eq_SomeI:
  assumes "r \<in> Y" "r bs = Some xn"
  assumes "\<And>r' xn'. r' \<in> Y \<Longrightarrow> r' bs = Some xn' \<Longrightarrow> xn' = xn"
  shows   "lub_pmfsr bs = Some xn"
proof -
  have *: "{xn |xn r. r \<in> Y \<and> r bs = Some xn} = {xn}"
    using assms by blast
  show ?thesis
    unfolding Let_def lub_pmfsr_def * by auto
qed

lemma lub_pmfsr_eq_SomeI':
  assumes "r \<in> Y" "r bs = Some xn" "Complete_Partial_Order.chain ord_pmfsr Y"
  shows   "lub_pmfsr bs = Some xn"
proof (rule lub_pmfsr_eq_SomeI[OF assms(1,2)])
  fix r' xn' assume r': "r' \<in> Y" "r' bs = Some xn'"
  with assms have "ord_pmfsr r r' \<or> ord_pmfsr r' r"
    by (auto simp: Complete_Partial_Order.chain_def)
  thus "xn' = xn"
    using ord_pmfsrD r' assms by (metis option.inject ord_pmfsrD)
qed

lemma lub_pmfsr_eq_SomeE:
  assumes "lub_pmfsr bs = Some xn"
  obtains r where "r \<in> Y" "r bs = Some xn"
  using assms
  by (auto simp: lub_pmfsr_def Let_def is_singleton_def split: if_splits)

lemma lub_pmfsr_eq_SomeD:
  assumes "lub_pmfsr bs = Some xn" "r \<in> Y" "r bs = Some xn'"
  shows   "xn' = xn"
proof -
  let ?X = "{xn |xn r. r \<in> Y \<and> r bs = Some xn}"
  from assms(1) have "is_singleton ?X"
    by (auto simp: lub_pmfsr_def Let_def split: if_splits)
  then obtain xn'' where xn'': "?X = {xn''}"
    by (auto simp: is_singleton_def)
  moreover have "xn' \<in> ?X"
    using assms by auto
  ultimately show "xn' = xn"
    using assms unfolding lub_pmfsr_def Let_def xn'' by auto
qed

end

lemma wf_lub_pmfsr:
  assumes "\<And>y. y \<in> Y \<Longrightarrow> ord_pmfsr y lub" "\<And>r. r \<in> Y \<Longrightarrow> wf_pmfsr r"
  shows   "wf_pmfsr (lub_pmfsr Y)"
proof (rule wf_pmfsrI)
  fix bs bs' x n
  assume *: "lub_pmfsr Y bs = Some (x, n)" "stake n bs' = stake n bs"
  from *(1) obtain r where r: "r \<in> Y" "r bs = Some (x, n)"
    by (auto elim!: lub_pmfsr_eq_SomeE)
  show "lub_pmfsr Y bs' = Some (x, n)"
  proof (rule lub_pmfsr_eq_SomeI)
    show "r \<in> Y"
      by fact
    show "r bs' = Some (x, n)"
      by (rule wf_pmfsrD[where bs = bs]) (use assms r * in auto)
    fix r' xn'
    assume r': "r' \<in> Y" "r' bs' = Some xn'"
    show "xn' = (x, n)"
      using \<open>r bs' = Some (x, n)\<close> r r'  assms(1)[of r] assms(1)[of r']
            ord_pmfsrD[of r lub bs' "(x, n)"] ord_pmfsrD[of r' lub bs' xn'] by simp
  qed
qed    

lemma wf_lub_pmfsr':
  assumes "Complete_Partial_Order.chain ord_pmfsr Y" "\<And>r. r \<in> Y \<Longrightarrow> wf_pmfsr r"
  shows   "wf_pmfsr (lub_pmfsr Y)"
proof (rule wf_pmfsrI)
  fix bs bs' x n
  assume *: "lub_pmfsr Y bs = Some (x, n)" "stake n bs' = stake n bs"
  from *(1) obtain r where r: "r \<in> Y" "r bs = Some (x, n)"
    by (auto elim!: lub_pmfsr_eq_SomeE)
  show "lub_pmfsr Y bs' = Some (x, n)"
  proof (rule lub_pmfsr_eq_SomeI)
    show "r \<in> Y"
      by fact
    show "r bs' = Some (x, n)"
      by (rule wf_pmfsrD[where bs = bs]) (use assms r * in auto)
    fix r' xn'
    assume r': "r' \<in> Y" "r' bs' = Some xn'"
    have "ord_pmfsr r' r \<or> ord_pmfsr r r'"
      using assms r r' by (auto simp: Complete_Partial_Order.chain_def)
    hence "ord_option (=) (r' bs') (r bs') \<or> ord_option (=) (r bs') (r' bs')"
      by (auto simp: ord_pmfsr_def rel_fun_def)
    thus "xn' = (x, n)"
      using \<open>r bs' = Some (x, n)\<close> r' by (cases "r' bs'") auto
  qed
qed    


lemma lub_pmfsr_empty [simp]: "lub_pmfsr {} = (\<lambda>_. None)"
  by (auto simp: lub_pmfsr_def fun_eq_iff is_singleton_def)

lemma lub_pmfsr_const [simp]: "lub_pmfsr {p} = p"
proof
  fix bs :: "bool stream"
  show "lub_pmfsr {p} bs = p bs"
  proof (cases "p bs")
    case None
    hence *: "{xn |xn r. r \<in> {p} \<and> r bs = Some xn} = {}"
      by auto
    show ?thesis
      unfolding lub_pmfsr_def Let_def * by (auto simp: is_singleton_def None)
  next
    case (Some xn)
    hence *: "{xn |xn r. r \<in> {p} \<and> r bs = Some xn} = {xn}"
      by auto
    show ?thesis
      unfolding lub_pmfsr_def Let_def * by (auto simp: is_singleton_def Some)
  qed
qed

lemma lub_pmfsr_upper':
  assumes Y: "Complete_Partial_Order.chain ord_pmfsr Y" "r \<in> Y"
  shows   "ord_pmfsr r (lub_pmfsr Y)"
  unfolding ord_pmfsr_def rel_fun_def
proof safe
  let ?R = "ord_pmfsr :: 'a pmfsr \<Rightarrow> _"
  fix bs :: "bool stream"
  show "ord_option (=) (r bs) (lub_pmfsr Y bs)"
  proof (cases "r bs")
    case None
    thus ?thesis
      by auto
  next
    case [simp]: (Some xn)
    have "{xn |xn r. r \<in> Y \<and> r bs = Some xn} = {xn}"
    proof (intro equalityI subsetI)
      fix xn' assume "xn' \<in> {xn |xn r. r \<in> Y \<and> r bs = Some xn}"
      then obtain r' where *: "r' \<in> Y" "r' bs = Some xn'"
        by auto
      from Y * have "ord_pmfsr r r' \<or> ord_pmfsr r' r"
        unfolding Complete_Partial_Order.chain_def by blast
      hence "ord_option (=) (r bs) (r' bs) \<or> ord_option (=) (r' bs) (r bs)"
        unfolding ord_pmfsr_def rel_fun_def by blast
      with * have "xn = xn'"
        by auto
      thus "xn' \<in> {xn}"
        by simp
    qed (use Y(2) in auto)
    hence "lub_pmfsr Y bs = Some xn"
      by (simp add: lub_pmfsr_def)
    thus ?thesis
      by simp
  qed
qed

lemma lub_pmfsr_least:
  assumes "\<And>r'. r' \<in> Y \<Longrightarrow> ord_pmfsr r' r"
  shows   "ord_pmfsr (lub_pmfsr Y) r"
  unfolding ord_pmfsr_def rel_fun_def
proof safe
  let ?R = "ord_pmfsr :: 'a pmfsr \<Rightarrow> _"
  fix bs :: "bool stream"
  show "ord_option (=) (lub_pmfsr Y bs) (r bs)"
  proof (cases "lub_pmfsr Y bs")
    case None
    thus ?thesis
      by auto
  next
    case (Some xn)
    then obtain r' where r': "r' \<in> Y" "r' bs = Some xn"
      by (elim lub_pmfsr_eq_SomeE)
    thus ?thesis
      unfolding Some using assms ord_pmfsrD by fastforce
  qed
qed

lemma lub_pmfsr_upper:
  assumes "\<And>r'. r' \<in> Y \<Longrightarrow> ord_pmfsr r' lub" "r \<in> Y"
  shows   "ord_pmfsr r (lub_pmfsr Y)"
  unfolding ord_pmfsr_def rel_fun_def
proof safe
  fix bs :: "bool stream"
  show "ord_option (=) (r bs) (lub_pmfsr Y bs)"
  proof (cases "r bs")
    case (Some xn)
    have "ord_pmfsr r lub"
      by (rule assms) fact
    have [simp]: "lub bs = Some xn"
      using \<open>ord_pmfsr r lub\<close> local.Some ord_pmfsrD by blast
    have [simp]: "lub_pmfsr Y bs = Some xn"
      by (rule lub_pmfsr_eq_SomeI[OF assms(2) Some])
         (use ord_pmfsrD[OF assms(1), of _ bs] in auto)
    show "ord_option (=) (r bs) (lub_pmfsr Y bs)"
      using Some by auto
  qed auto
qed

lemma partial_function_definitions_pmfsr: 
  "partial_function_definitions ord_pmfsr lub_pmfsr"
  (is "partial_function_definitions ?R _")
proof
  fix x show "?R x x"
    by (auto simp: ord_pmfsr_def rel_fun_def intro: ord_option_reflI)
next
  fix x y z
  assume "?R x y" "?R y z"
  with transp_ord_option[OF transp_equality] show "?R x z"
    unfolding ord_pmfsr_def by (fastforce simp: rel_fun_def transp_def)    
next
  fix x y
  assume "?R x y" "?R y x"
  thus "x = y"
    using antisymp_ord_option[of "(=)"]
    by (fastforce simp: ord_pmfsr_def rel_fun_def antisymp_def)
qed (use lub_pmfsr_upper' lub_pmfsr_least in blast)+

lemma ccpo_pmfsr: "class.ccpo lub_pmfsr ord_pmfsr (mk_less ord_pmfsr)"
  by (rule ccpo partial_function_definitions_pmfsr)+



instantiation sampler :: (type) order
begin

lift_definition less_eq_sampler :: "'a sampler \<Rightarrow> 'a sampler \<Rightarrow> bool" is ord_pmfsr .

lift_definition less_sampler :: "'a sampler \<Rightarrow> 'a sampler \<Rightarrow> bool" is
   "mk_less ord_pmfsr" .

instance proof -
  interpret pmfsr: ccpo lub_pmfsr ord_pmfsr "mk_less ord_pmfsr"
    by (rule ccpo_pmfsr)
  show "OFCLASS('a sampler, order_class)"
  proof
    fix x y :: "'a sampler"
    show "x < y \<longleftrightarrow> x \<le> y \<and> \<not>y \<le> x"
      by transfer auto    
  next
    fix x :: "'a sampler" show "x \<le> x"
      by transfer (rule pmfsr.order.refl)
  next
    fix x y z :: "'a sampler"
    assume "x \<le> y" "y \<le> z"
    thus "x \<le> z"
      by transfer (rule pmfsr.order.trans)    
  next
    fix x y :: "'a sampler"
    assume "x \<le> y" "y \<le> x"
    thus "x = y"
      by transfer (rule pmfsr.order.antisym)
  qed
qed

end

lemma less_eq_sampler_altdef:
  "p \<le> q \<longleftrightarrow> (\<forall>bs. ord_option (=) (run_sampler p bs) (run_sampler q bs))"
  by transfer (auto simp: ord_pmfsr_def rel_fun_def)



definition compatible_sampler :: "'a sampler set \<Rightarrow> bool" where
  "compatible_sampler Y \<longleftrightarrow> (\<exists>p. \<forall>q\<in>Y. q \<le> p)"

lemma compatible_samplerI [intro?]: "(\<And>q. q \<in> Y \<Longrightarrow> q \<le> p) \<Longrightarrow> compatible_sampler Y"
  by (auto simp: compatible_sampler_def)

lemma wf_pmfsr_run_sampler [intro]: "wf_pmfsr (run_sampler p)"
  by transfer auto

lemma chain_imp_compatible_sampler:
  assumes "Complete_Partial_Order.chain (\<le>) Y"
  shows   "compatible_sampler Y"
proof
  interpret pmfsr: ccpo lub_pmfsr ord_pmfsr "mk_less ord_pmfsr"
    by (rule ccpo_pmfsr)
  have chain: "Complete_Partial_Order.chain ord_pmfsr (run_sampler ` Y)"
    by (intro chain_imageI[OF assms])
       (auto simp: ord_pmfsr_def rel_fun_def less_eq_sampler_altdef)

  fix q assume q: "q \<in> Y"
  have "ord_pmfsr (run_sampler q) (lub_pmfsr (run_sampler ` Y))"
    using assms q chain by (intro pmfsr.ccpo_Sup_upper) auto
  moreover have "wf_pmfsr (lub_pmfsr (run_sampler ` Y))"
    by (intro wf_lub_pmfsr' chain) auto
  ultimately show "q \<le> Abs_sampler (lub_pmfsr (run_sampler ` Y))"
    by (simp add: Abs_sampler_inverse less_eq_sampler.rep_eq run_sampler.rep_eq)
qed

instantiation sampler :: (type) Sup
begin

lift_definition Sup_sampler :: "'a sampler set \<Rightarrow> 'a sampler" is
  "\<lambda>Y. if \<exists>lub. \<forall>y\<in>Y. ord_pmfsr y lub then lub_pmfsr Y else (\<lambda>_. None)"
  using wf_lub_pmfsr by auto

instance ..

end

lemma Sup_sampler_upper:
  assumes "compatible_sampler Y" "p \<in> Y"
  shows   "p \<le> Sup Y"
  using assms unfolding compatible_sampler_def
  apply transfer
  apply auto
  using lub_pmfsr_upper by blast

lemma Sup_sampler_least:
  assumes "\<And>q::'a sampler. q \<in> Y \<Longrightarrow> q \<le> p"
  shows   "Sup Y \<le> p"
  using assms
  apply transfer
  apply (auto)
  using lub_pmfsr_least apply blast+
  done

instance sampler :: (type) ccpo
  by intro_classes (use Sup_sampler_upper Sup_sampler_least chain_imp_compatible_sampler in meson)+



instantiation sampler :: (type) order_bot
begin

lift_definition bot_sampler :: "'a sampler" is "\<lambda>_. None"
  by (rule wf_pmfsr_const_None)

instance proof
  fix p :: "'a sampler"
  show "bot \<le> p"
    by transfer (auto simp: ord_pmfsr_def)
qed

end

lemma Sup_sampler_empty [simp]: "Sup {} = (bot :: 'a sampler)"
  by transfer auto

lemma run_sampler_bot [simp]: "run_sampler bot = (\<lambda>_. None)"
  by transfer auto

lemma map_sampler_bot [simp]: "map_sampler f bot = bot"
  by (rule sampler_eqI) auto

lemma map_sampler_id [simp]: "map_sampler id p = p"
  by (rule sampler_eqI) (auto simp: map_prod_def map_option.id)

lemma map_sampler_id' [simp]: "map_sampler (\<lambda>x. x) p = p"
  by (rule sampler_eqI) (auto simp: map_prod_def map_option.id)

lemma bind_sampler_bot [simp]: "bind_sampler bot f = bot"
  by transfer auto

lemma bind_sampler_bot' [simp]: "bind_sampler f (\<lambda>_. bot) = bot"
  by transfer (auto simp: fun_eq_iff Option_bind_conv_case split: option.splits)



lemma le_samplerD1:
  assumes "p \<le> q" "run_sampler p bs = Some xn"
  shows   "run_sampler q bs = Some xn"
  using assms unfolding less_eq_sampler_altdef
  by (metis ord_option_eq_simps(2))

lemma le_samplerD2:
  assumes "p \<le> q" "run_sampler q bs = None"
  shows   "run_sampler p bs = None"
  using assms unfolding less_eq_sampler_altdef
  by (metis ord_option_simps(2))




lift_definition range_sampler :: "'a sampler \<Rightarrow> 'a set" is "\<lambda>r. fst ` Some -` range r" .

lemma range_sampler_altdef: "range_sampler r = fst ` Some -` range (run_sampler r)"
  by transfer auto

lemma in_range_samplerI:
  assumes "run_sampler r bs = Some (x, n)"
  shows   "x \<in> range_sampler r"
  unfolding range_sampler_altdef
  by (rule image_eqI[of _ _ "(x, n)"]) (use assms in \<open>auto intro: image_eqI[of _ _ bs]\<close>)

lemma in_range_samplerE:
  assumes "x \<in> range_sampler r"
  obtains bs n where "run_sampler r bs = Some (x, n)"
  using assms unfolding range_sampler_altdef by (auto simp: eq_commute)

lemma range_sampler_altdef': "range_sampler r = {x |x bs n. run_sampler r bs = Some (x, n)}"
  by (blast elim: in_range_samplerE intro: in_range_samplerI)
  

lemma exists_sprefix_right [intro]: "\<exists>ys. sprefix xs ys"
  by (rule exI[of _ "xs @- sconst undefined"]) auto

lemma range_sampler_bot [simp]:
  "range_sampler bot = {}"
  unfolding range_sampler_altdef' by auto

lemma range_sampler_map [simp]:
  "range_sampler (map_sampler f p) = f ` range_sampler p"
  unfolding range_sampler_altdef' by auto

lemma range_sampler_singleton [simp]:
  "range_sampler (singleton_sampler bs) = {bs}"
  unfolding range_sampler_altdef' by (auto simp: run_sampler_singleton)

lemma range_sampler_of_ptree [simp]:
  "range_sampler (sampler_of_ptree t) = set_ptree t"
  unfolding range_sampler_altdef' by (auto simp: run_sampler_of_ptree prefix_of_ptree_simps)

lemma in_range_sampler: "run_sampler r bs \<in> options (range_sampler r \<times> UNIV)"
proof (cases "run_sampler r bs")
  case [simp]: (Some z)
  obtain y n where [simp]: "z = (y, n)"
    by (cases z)
  have "y \<in> range_sampler r"
    by (rule in_range_samplerI[of _ bs _ n]) auto
  thus ?thesis
    by auto
qed auto

lemma countable_range_pmfsr [intro]: "countable (range_sampler r)"
  by (cases r) auto

lemma range_run_sampler_subset:
  "range (run_sampler r) \<subseteq> options (range_sampler r \<times> UNIV)"
  using in_range_sampler by blast

lemma complement_in_sets_coin_space: "X \<in> sets coin_space \<Longrightarrow> -X \<in> sets coin_space"
  by (metis Compl_eq_Diff_UNIV sets.compl_sets space_coin_space)

lemma measurable_prefix_of_ptree [measurable]:
  "prefix_of_ptree t \<in> coin_space \<rightarrow>\<^sub>M count_space UNIV"
  unfolding measurable_def
proof safe
  fix X :: "bool list option set"
  have *: "prefix_of_ptree t -` Some ` X \<in> sets coin_space" for X
  proof -
    have "prefix_of_ptree t -` Some ` X = (\<Union>bs\<in>X\<inter>set_ptree t. stake (length bs) -` {bs})"
      by (auto simp: prefix_of_ptree_simps sprefix_def)
    also have "\<dots> \<in> sets coin_space"
      by (intro sets.countable_UN)
         (auto intro!: measurable_sets_coin_space[of _ "count_space UNIV"])
    finally show ?thesis .
  qed

  have **: "prefix_of_ptree t -` X \<in> sets coin_space" if "None \<notin> X" for X
  proof -
    have "prefix_of_ptree t -` Some ` Some -` X \<in> sets coin_space"
      by (rule *)
    also have "Some ` Some -` X = X"
      using that by (auto simp: range_Some)
    finally show ?thesis .
  qed

  show "prefix_of_ptree t -` X \<inter> space coin_space \<in> coin_space.events"
  proof (cases "None \<in> X")
    case True
    have "-(prefix_of_ptree t -` (-X)) \<in> coin_space.events"
      using True by (intro complement_in_sets_coin_space **) auto
    also have "-(prefix_of_ptree t -` (-X)) = prefix_of_ptree t -` X"
      by auto
    finally show ?thesis
      by (simp add: space_coin_space)
  qed (auto simp: space_coin_space intro: **)
qed auto
  
lemma measurable_run_sampler [measurable]:
  "run_sampler r \<in> coin_space \<rightarrow>\<^sub>M count_space UNIV"
proof (cases r)
  case (1 f t)
  have "coin_space.random_variable (count_space UNIV)
          (map_option (map_prod f id \<circ> (\<lambda>bs'. (bs', length bs'))) \<circ> prefix_of_ptree t)"
    by measurable
  thus ?thesis using 1
    by (simp add: run_sampler_of_ptree o_assoc map_option.comp)
qed






lemma range_sampler_mono:
  assumes "p \<le> q"
  shows   "range_sampler p \<subseteq> range_sampler q"
  using assms by (metis in_range_samplerE subsetI in_range_samplerI le_samplerD1)

lemma map_sampler_mono:
  assumes "p \<le> q"
  shows   "map_sampler f p \<le> map_sampler f q"
  using assms unfolding less_eq_sampler_altdef
  by (rule all_forward) (auto simp: ord_option_case split: option.splits)

lemma less_eq_ptree_altdef: "t \<le> t' \<longleftrightarrow> set_ptree t \<subseteq> set_ptree t'"
  by (simp add: less_eq_ptree.rep_eq)

lemma prefix_of_ptree_mono:
  assumes "t \<le> t'"
  shows   "ord_option (=) (prefix_of_ptree t xs) (prefix_of_ptree t' xs)"
  using assms unfolding less_eq_ptree_altdef
  apply (auto simp: ord_option_case prefix_of_ptree_simps split: option.splits)
  apply (metis in_mono option.inject prefix_of_ptree_eq_SomeI)
  done

lemma bind_sampler_mono_strong:
  "p \<le> p' \<Longrightarrow> (\<And>x. x \<in> range_sampler p \<Longrightarrow> q x \<le> q' x) \<Longrightarrow> bind_sampler p q \<le> bind_sampler p' q'"
  sorry

lemma bind_sampler_mono:
  "p \<le> p' \<Longrightarrow> (\<And>x. q x \<le> q' x) \<Longrightarrow> bind_sampler p q \<le> bind_sampler p' q'"
  by (rule bind_sampler_mono_strong)

lemma map_option_mono':
  "ord_option rel x y \<Longrightarrow> monotone rel rel' f \<Longrightarrow>
   ord_option rel' (map_option f x) (map_option f y)"
  by (auto simp: ord_option_case monotone_def split: option.splits)

lemma map_sampler_eq_bot_iff [simp]: "map_sampler f p = bot \<longleftrightarrow> p = bot"
proof
  assume *: "map_sampler f p = bot"
  have "run_sampler p bs = None" for bs
  proof -
    have "map_option (map_prod f id) (run_sampler p bs) = run_sampler (map_sampler f p) bs"
      by simp
    also have "\<dots> = None"
      by (subst *) auto
    finally show ?thesis by simp
  qed
  thus "p = bot"
    by (intro sampler_eqI) auto
qed auto

lemma ptree_of_sampler_bot [simp]: "ptree_of_sampler bot = bot"
  by (metis map_sampler_eq_bot_iff range_sampler_bot range_sampler_of_ptree 
            sampler_decompose set_ptree_bot set_ptree_inverse)



lemma sampler_of_ptree_le_iff [simp]: "sampler_of_ptree t \<le> sampler_of_ptree t' \<longleftrightarrow> t \<le> t'"
proof
  assume le: "t \<le> t'"
  show "sampler_of_ptree t \<le> sampler_of_ptree t'"
    unfolding less_eq_sampler_altdef run_sampler_of_ptree o_apply
    by (rule allI map_option_mono' prefix_of_ptree_mono le monotoneI)+ auto
next
  assume le: "sampler_of_ptree t \<le> sampler_of_ptree t'"
  thus "t \<le> t'"
    unfolding less_eq_ptree_altdef using range_sampler_mono range_sampler_of_ptree by blast
qed

lemma sampler_of_ptree_mono: "t \<le> t' \<Longrightarrow> sampler_of_ptree t \<le> sampler_of_ptree t'"
  by simp

lemma run_sampler_mono: "p \<le> q \<Longrightarrow> ord_pmfsr (run_sampler p) (run_sampler q)"
  by transfer auto

lemma chain_sampler_of_ptree:
  assumes "Complete_Partial_Order.chain (\<le>) Y"
  shows   "Complete_Partial_Order.chain (\<le>) (sampler_of_ptree ` Y)"
  using assms by (intro chain_imageI sampler_of_ptree_mono)

context
  fixes Y :: "'a sampler set"
  assumes Y: "compatible_sampler Y"
begin

lemma run_sampler_Sup:
  "run_sampler (Sup Y) = lub_pmfsr (run_sampler ` Y)"
  using Y unfolding compatible_sampler_def by transfer auto

lemma run_sampler_Sup':
   "run_sampler (Sup Y) bs = the_elem' {xn. \<exists>r\<in>Y. run_sampler r bs = Some xn}"
  by (simp add: run_sampler_Sup lub_pmfsr_def Let_def the_elem'_def)

lemma run_sampler_Sup_eq_SomeI:
  "run_sampler p bs = Some xn \<Longrightarrow> p \<in> Y \<Longrightarrow> run_sampler (Sup Y) bs = Some xn"
  using Sup_sampler_upper Y le_samplerD1 by blast

lemma run_sampler_Sup_eq_SomeE:
  assumes "run_sampler (Sup Y) bs = Some xn"
  obtains p where "p \<in> Y" "run_sampler p bs = Some xn"
  using assms by (auto simp: run_sampler_Sup elim!: lub_pmfsr_eq_SomeE)

lemma run_sampler_Sup_eq_Some_iff:
  "run_sampler (Sup Y) bs = Some xn \<longleftrightarrow> (\<exists>p\<in>Y. run_sampler p bs = Some xn)"
  by (auto intro: run_sampler_Sup_eq_SomeI elim: run_sampler_Sup_eq_SomeE)

lemma run_sampler_Sup_eq_None_iff:
  "run_sampler (Sup Y) bs = None \<longleftrightarrow> (\<forall>p\<in>Y. run_sampler p bs = None)"
  by (metis not_Some_eq run_sampler_Sup_eq_Some_iff)

lemmas run_sampler_Sup_simps = run_sampler_Sup_eq_None_iff run_sampler_Sup_eq_Some_iff

end

lemma compatible_sampler_map [intro]:
  "compatible_sampler Y \<Longrightarrow> compatible_sampler (map_sampler f ` Y)"
  unfolding compatible_sampler_def using map_sampler_mono by blast

lemma Sup_map_sampler:
  assumes Y: "compatible_sampler Y"
  shows   "Sup (map_sampler f ` Y) = map_sampler f (Sup Y)"
proof (rule sampler_eqI)
  fix bs :: "bool stream"
  show "run_sampler (Sup (map_sampler f ` Y)) bs = run_sampler (map_sampler f (Sup Y)) bs"
    using Y by (fastforce simp: run_sampler_Sup_simps map_option_case 
                                compatible_sampler_map split: option.splits)
qed


(* TODO Move *)
lemma set_ptree_sprefixD:
  assumes "xs \<in> set_ptree t" "xs' \<in> set_ptree t" "sprefix xs ys" "sprefix xs' ys"
  shows   "xs' = xs"
  using assms by (metis set_ptreeD sprefix_altdef sprefix_shiftD)

(* TODO Move *)
lemma set_ptree_sprefixD':
  assumes "xs \<in> set_ptree t" "xs' \<in> set_ptree t" "sprefix xs ys"
  shows   "sprefix xs' ys \<longleftrightarrow> xs' = xs"
  using assms by (metis set_ptreeD sprefix_altdef sprefix_shiftD)

lemma compatible_sampler_of_ptree [intro]:
  "ptree_compatible Y \<Longrightarrow> compatible_sampler (sampler_of_ptree ` Y)"
  by (rule compatible_samplerI[of _ "sampler_of_ptree (Sup Y)"])
     (auto intro: Sup_ptree_upper)
  
lemma sampler_of_ptree_Sup:
  assumes "ptree_compatible Y"
  shows   "sampler_of_ptree (Sup Y) = Sup (sampler_of_ptree ` Y)"
proof (rule sym, rule sampler_eqI)
  fix bs
  show "run_sampler (\<Squnion> (sampler_of_ptree ` Y)) bs = run_sampler (sampler_of_ptree (\<Squnion> Y)) bs"
    using assms
    by (auto simp: run_sampler_of_ptree map_option_case prefix_of_ptree_simps set_ptree_Sup
                   run_sampler_Sup_simps compatible_sampler_of_ptree
             split: option.splits dest: set_ptree_sprefixD)
qed




definition measure_ptree :: "bool ptree \<Rightarrow> bool list option measure" where
  "measure_ptree t = distr coin_space (count_space UNIV) (prefix_of_ptree t)"

lemma prob_space_measure_ptree [intro]: "prob_space (measure_ptree t)"
  unfolding measure_ptree_def by (rule coin_space.prob_space_distr) measurable

lemma space_measure_ptree [simp]: "space (measure_ptree t) = UNIV"
  by (auto simp: measure_ptree_def)

lemma sets_measure_ptree [measurable_cong]:
  "sets (measure_ptree t) = sets (count_space UNIV)"
  by (auto simp: measure_ptree_def)

interpretation ptree: prob_space "measure_ptree t" ..

lemma prefix_of_ptree_in_image_Some_iff:
  "prefix_of_ptree t xs \<in> Some ` X \<longleftrightarrow> (\<exists>ys\<in>set_ptree t \<inter> X. sprefix ys xs)"
  by (cases "prefix_of_ptree t xs") (auto simp: prefix_of_ptree_simps)

lemma prob_ptree:
  "ptree.prob t (Some ` X) =
     coin_space.prob {bs |bs bs'. sprefix bs' bs \<and> bs' \<in> set_ptree t \<inter> X}"
proof -
  have "ptree.prob t (Some ` X) = coin_space.prob (prefix_of_ptree t -` Some ` X)"
    by (auto simp: measure_ptree_def measure_distr space_coin_space)
  also have "prefix_of_ptree t -` Some ` X = {bs |bs bs'. sprefix bs' bs \<and> bs' \<in> set_ptree t \<inter> X}"
    by (fastforce simp: prefix_of_ptree_simps prefix_of_ptree_in_image_Some_iff
                        sprefix_imp_stake_eq intro: sprefixI)
  finally show ?thesis .
qed

context
begin

interpretation pmf_as_measure .

lift_definition spmf_of_ptree :: "bool ptree \<Rightarrow> bool list spmf" is measure_ptree
proof (intro conjI, goal_cases)
  fix t :: "bool ptree"
  show "AE x in measure_ptree t. ptree.prob t {x} \<noteq> 0 "
    by (subst ptree.AE_support_countable) auto
qed auto

lemma spmf_spmf_of_ptree:
  "spmf (spmf_of_ptree t) bs = indicator (set_ptree t) bs / 2 ^ length bs"
proof -
  have "spmf (spmf_of_ptree t) bs = ptree.prob t {Some bs}"
    by (simp add: pmf.rep_eq spmf_of_ptree.rep_eq)
  also have "{Some bs} = Some ` {bs}"
    by simp
  also have "ptree.prob t \<dots> =
               coin_space.prob {bs'' |bs'' bs'. sprefix bs' bs'' \<and> bs' \<in> set_ptree t \<inter> {bs}}"
    by (subst prob_ptree) auto
  also have "{bs'' |bs'' bs'. sprefix bs' bs'' \<and> bs' \<in> set_ptree t \<inter> {bs}} =
               (if bs \<in> set_ptree t then stake (length bs) -` {bs} else {})"
    by (auto simp: sprefix_def)
  also have "coin_space.prob \<dots> = 
               indicator (set_ptree t) bs * coin_space.prob (stake (length bs) -` {bs})"
    by (auto simp: indicator_def)
  also have "coin_space.prob (stake (length bs) -` {bs}) = 1 / 2 ^ length bs"
    using emeasure_coin_space_stake[of "{bs}" "length bs"]
    by (auto simp: coin_space.emeasure_eq_measure)
  finally show ?thesis
    by simp
qed

lemma spmf_of_ptree_mono: 
  assumes "x \<le> y"
  shows   "ord_spmf (=) (spmf_of_ptree x) (spmf_of_ptree y)"
proof (rule ord_pmf_increaseI)
  fix bs
  show "spmf (spmf_of_ptree x) bs \<le> spmf (spmf_of_ptree y) bs"
    using assms by (auto simp: spmf_spmf_of_ptree indicator_def less_eq_ptree_altdef)
qed auto

lemma set_pmf_of_ptree [simp]: "set_spmf (spmf_of_ptree t) = set_ptree t"
  by (auto simp: in_set_spmf_iff_spmf spmf_spmf_of_ptree indicator_def)

lemma spmf_of_ptree_le_iff: "ord_spmf (=) (spmf_of_ptree x) (spmf_of_ptree y) \<longleftrightarrow> x \<le> y"
  by (metis less_eq_ptree.rep_eq ord_spmf_eqD_set_spmf set_pmf_of_ptree spmf_of_ptree_mono)

lemma spmf_of_ptree_bot [simp]: "spmf_of_ptree bot = return_pmf None"
  by (intro spmf_eqI) (auto simp: spmf_spmf_of_ptree)

lemma spmf_of_ptree_of_length [simp]:
  "spmf_of_ptree (ptree_of_length n) = spmf_of_set {bs. length bs = n}"
proof (rule spmf_eqI)
  fix bs :: "bool list"
  show "spmf (spmf_of_ptree (ptree_of_length n)) bs = spmf (spmf_of_set {bs. length bs = n}) bs"
    using card_lists_length_eq[of "UNIV :: bool set", of n]
    by (subst spmf_of_set) (auto simp: spmf_spmf_of_ptree)
qed

lemma spmf_of_ptree_singleton_Nil [simp]: "spmf_of_ptree (singleton_ptree []) = return_spmf []"
  by (subst ptree_of_length_0 [symmetric], subst spmf_of_ptree_of_length)
     (simp_all add: spmf_of_set_singleton)

end


lemma countableE:
  assumes "countable A" "A \<noteq> {}"
  obtains f :: "nat \<Rightarrow> 'a" where "range f = A"
  using assms by (meson uncountable_def)

lemma sup_0_ennreal [simp]: "sup 0 (x :: ennreal) = x" "sup x 0 = x"
  by (simp_all add: sup.absorb1 sup.absorb2)

lemma spmf_of_ptree_Sup:
  assumes chain: "Complete_Partial_Order.chain (\<le>) Y"
  shows   "spmf_of_ptree (Sup Y) = lub_spmf (spmf_of_ptree ` Y)" (is "?lhs = ?rhs")
proof (rule spmf_eqI)
  fix bs :: "bool list"
  have chain': "Complete_Partial_Order.chain (ord_spmf (=)) (spmf_of_ptree ` Y)"
    by (rule chain_imageI[OF chain] spmf_of_ptree_mono)+
  note [simp] = ptree_chain_imp_compatible[OF chain]

  show "spmf ?lhs bs = spmf ?rhs bs"
  proof (cases "bs \<in> (\<Union>t\<in>Y. set_ptree t)")
    case False
    hence "bs \<notin> set_spmf ?lhs" "bs \<notin> set_spmf ?rhs"
      by (auto simp: set_lub_spmf[OF chain'] set_ptree_Sup)
    thus ?thesis
      by (metis spmf_eq_0_set_spmf)
  next
    case True
    hence [simp]: "Y \<noteq> {}"
      by auto
    have "spmf ?lhs bs = 1 / 2 ^ length bs"
      using True by (simp add: spmf_spmf_of_ptree indicator_def set_ptree_Sup)
    have "ennreal (spmf ?rhs bs) = \<Squnion> ((\<lambda>t. ennreal (spmf (spmf_of_ptree t) bs)) ` Y)"
      by (simp add: ennreal_spmf_lub_spmf chain' image_image)
    also have "(\<lambda>t. ennreal (spmf (spmf_of_ptree t) bs)) ` Y =
                 (if \<exists>t\<in>Y. bs \<notin> set_ptree t then {0} else {}) \<union>
                 {ennreal (1 / 2 ^ length bs)}"
      using True by (auto simp: spmf_spmf_of_ptree indicator_def)
    also have "\<Squnion>\<dots> = ennreal (1 / 2 ^ length bs)"
      by auto
    also have "\<dots> = ennreal (spmf ?lhs bs)"
      using True by (simp add: spmf_spmf_of_ptree indicator_def set_ptree_Sup)
    finally show ?thesis
      by simp
  qed
qed
  

  





definition measure_sampler :: "'a sampler \<Rightarrow> 'a option measure" where
  "measure_sampler p = distr coin_space (count_space UNIV) (map_option fst \<circ> run_sampler p)"

definition spmf_of_sampler :: "'a sampler \<Rightarrow> 'a spmf" where
  "spmf_of_sampler p = map_spmf (fun_sampler p) (spmf_of_ptree (ptree_of_sampler p))"

lemma measure_pmf_of_ptree: "measure_pmf (spmf_of_ptree t) = measure_ptree t"
  by (simp add: spmf_of_ptree.rep_eq)

lemma spmf_spmf_of_sampler:
  "spmf (spmf_of_sampler p) x = coin_space.prob {bs'. \<exists>n. run_sampler p bs' = Some (x, n)}"
proof -
  define t where "t = ptree_of_sampler p"
  define f where "f = fun_sampler p"
  have p_eq: "p = map_sampler f (sampler_of_ptree t)"
    by (simp add: f_def t_def flip: sampler_decompose)

  have "spmf (spmf_of_sampler p) x = ptree.prob t (Some ` f -` {x})"
    by (simp add: spmf_of_sampler_def spmf_map measure_measure_spmf_conv_measure_pmf
                  measure_pmf_of_ptree t_def f_def)
  also have "\<dots> = coin_space.prob (Collect (\<lambda>bs'. \<exists>bs\<in>set_ptree t. sprefix bs bs' \<and> f bs = x))"
    unfolding prob_ptree by (rule arg_cong[of _ _ coin_space.prob]) auto
  also have "Collect (\<lambda>bs'. \<exists>bs\<in>set_ptree t. sprefix bs bs' \<and> f bs = x) =
             Collect (\<lambda>bs'. \<exists>n. run_sampler p bs' = Some (x, n))"
    by (intro arg_cong[of _ _ Collect] ext)
       (auto simp: p_eq run_sampler_of_ptree prefix_of_ptree_simps)
  finally show ?thesis .
qed

lemma spmf_of_samler_bot [simp]: "spmf_of_sampler bot = return_pmf None"
  by (simp add: spmf_of_sampler_def )

lemma map_sampler_cong [cong]:
  "(\<And>x. x \<in> range_sampler p \<Longrightarrow> f x = g x) \<Longrightarrow> p = p' \<Longrightarrow> map_sampler f p = map_sampler g p'"
  by (rule sampler_eqI)
     (auto simp: map_option_case in_range_samplerI split: option.splits)

lemma le_imp_fun_sampler_eq:
  assumes "p \<le> q" "bs \<in> set_ptree (ptree_of_sampler p)"
  shows   "fun_sampler p bs = fun_sampler q bs"
  using assms unfolding fun_sampler_altdef set_ptree_of_sampler using le_samplerD1 by fastforce

lemma fun_sampler_return:
  "fun_sampler (return_sampler x) [] = x"
  by transfer (auto simp: map_option_case split: option.splits)

lemma fun_sampler_map:
  assumes "bs \<in> set_ptree (ptree_of_sampler p)"
  shows   "fun_sampler (map_sampler f p) bs = f (fun_sampler p bs)"
  using assms by transfer (auto simp: map_option_case split: option.splits)

lemma fun_sampler_of_ptree [simp]:
  assumes "bs \<in> set_ptree t"
  shows   "fun_sampler (sampler_of_ptree t) bs = bs"
  using assms 
  by transfer
     (auto simp: map_option_case prefix_of_ptree_simps
           dest: set_ptreeD sprefix_shiftD split: option.splits)


lemma spmf_of_sampler_welldefined:
  assumes "p = map_sampler f (sampler_of_ptree t)"
  shows   "spmf_of_sampler p = map_spmf f (spmf_of_ptree t)"
proof -
  have "spmf_of_sampler p = map_spmf (fun_sampler p) (spmf_of_ptree (ptree_of_sampler p))"
    by (simp add: spmf_of_sampler_def o_def)
  also have "ptree_of_sampler p = t"
    using assms by simp
  also have "map_spmf (fun_sampler p) (spmf_of_ptree t) = map_spmf f (spmf_of_ptree t)"
    by (rule map_spmf_cong) (auto simp: assms fun_sampler_map)
  finally show ?thesis by simp
qed

lemma spmf_of_sampler_return [simp]:
  "spmf_of_sampler (return_sampler x) = return_spmf x"
  by (subst spmf_of_sampler_welldefined[of _ "\<lambda>_. x" "singleton_ptree []"]) auto

lemma spmf_of_sampler_map [simp]:
  "spmf_of_sampler (map_sampler f p) = map_spmf f (spmf_of_sampler p)"
proof -
  have "spmf_of_sampler (map_sampler f p) =
          map_spmf (fun_sampler (map_sampler f p)) (spmf_of_ptree (ptree_of_sampler p))"
    by (simp add: spmf_of_sampler_def spmf.map_comp o_def )
  also have "\<dots> = map_spmf (f \<circ> fun_sampler p) (spmf_of_ptree (ptree_of_sampler p))"
    by (intro map_spmf_cong) (auto simp: fun_sampler_map)
  also have "\<dots> = map_spmf f (spmf_of_sampler p)"
    by (simp add: spmf_of_sampler_def spmf.map_comp)
  finally show ?thesis .
qed

lemma spmf_of_sampler_bind [simp]:
  "spmf_of_sampler (bind_sampler p q) = bind_spmf (spmf_of_sampler p) (spmf_of_sampler \<circ> q)"
  sorry

lemma spmf_of_sampler_of_ptree [simp]: "spmf_of_sampler (sampler_of_ptree t) = spmf_of_ptree t"
  by (subst spmf_of_sampler_welldefined[of _ id t]) auto

lemma ptree_of_sampler_mono:
  assumes "p \<le> q"
  shows   "ptree_of_sampler p \<le> ptree_of_sampler q"
proof -
  show ?thesis
    unfolding less_eq_ptree_altdef
  proof safe
    fix bs assume bs: "bs \<in> set_ptree (ptree_of_sampler p)"
    define bs' where "bs' = bs @- sconst False"
    from bs obtain x where x: "run_sampler p bs' = Some (x, length bs)"
      by (auto simp: set_ptree_of_sampler bs'_def)
    moreover have "ord_option (=) (run_sampler p bs') (run_sampler q bs')"
      using assms unfolding less_eq_sampler_altdef by blast
    ultimately show "bs \<in> set_ptree (ptree_of_sampler q)"
      by (auto simp: set_ptree_of_sampler bs'_def)
  qed
qed

lemma spmf_of_sampler_mono:
  assumes "p \<le> q"
  shows   "ord_spmf (=) (spmf_of_sampler p) (spmf_of_sampler q)"
proof (rule ord_pmf_increaseI)
  fix x :: 'a
  have *: "(\<exists>n. run_sampler q bs = Some (x, n))" if "(\<exists>n. run_sampler p bs = Some (x, n))" for bs
    by (rule ex_forward [OF that]) (use assms le_samplerD1 in blast)
  show "spmf (spmf_of_sampler p) x \<le> spmf (spmf_of_sampler q) x"
    unfolding spmf_spmf_of_sampler
  proof (rule coin_space.finite_measure_mono)
    have meas: "run_sampler q -` {Some (x, n)} \<inter> space coin_space \<in> coin_space.events" for n
      by measurable
    have "{bs'. \<exists>n. run_sampler q bs' = Some (x, n)} = (\<Union>n. run_sampler q -` {Some (x, n)})"
      by auto
    also have "\<dots> \<in> sets coin_space"
      using meas by (intro sets.countable_UN) (auto simp: space_coin_space)
    finally show "{bs'. \<exists>n. run_sampler q bs' = Some (x, n)} \<in> coin_space.events" .
  qed (use * in auto)
qed auto

lemma lub_spmf_of_sampler:
  assumes "Complete_Partial_Order.chain (\<le>) Y"
  shows   "lub_spmf (spmf_of_sampler ` Y) = spmf_of_sampler (Sup Y)"
proof -
  define Y' where "Y' = ptree_of_sampler ` Y"
  define f where "f = fun_sampler (Sup Y)"
  have "(\<lambda>x. x) ` Y = map_sampler f ` sampler_of_ptree ` Y'"
    unfolding Y'_def image_image
  proof (intro image_cong refl)
    fix p assume "p \<in> Y"
    hence le: "p \<le> \<Squnion>Y"
      using assms ccpo_Sup_upper by auto
    have "p = map_sampler (fun_sampler p) (sampler_of_ptree (ptree_of_sampler p))"
      by (simp flip: sampler_decompose)
    also have "\<dots> = map_sampler f (sampler_of_ptree (ptree_of_sampler p))"
      by (intro map_sampler_cong)
         (auto simp: f_def intro: le_imp_fun_sampler_eq[OF le])
    finally show "p = map_sampler f (sampler_of_ptree (ptree_of_sampler p))" .
  qed
  hence Y: "Y = map_sampler f ` sampler_of_ptree ` Y'"
    by simp
  have chain_Y': "Complete_Partial_Order.chain (\<le>) Y'"
    unfolding Y'_def by (rule chain_imageI[OF assms]) (auto intro: ptree_of_sampler_mono)

  have "lub_spmf (spmf_of_sampler ` Y) = lub_spmf (map_spmf f ` spmf_of_ptree ` Y')"
    by (simp add: Y image_image )
  also have "\<dots> = map_spmf f (lub_spmf (spmf_of_ptree ` Y'))"
    by (rule map_lub_spmf [symmetric] chain_imageI[OF chain_Y'] spmf_of_ptree_mono)+
  also have "lub_spmf (spmf_of_ptree ` Y') = spmf_of_ptree (Sup Y')"
    using chain_Y' by (rule spmf_of_ptree_Sup [symmetric])
  also have "map_spmf f (spmf_of_ptree (\<Squnion> Y')) =
             spmf_of_sampler (map_sampler f (sampler_of_ptree (\<Squnion>Y')))"
    by simp
  also have "map_sampler f (sampler_of_ptree (\<Squnion>Y')) = \<Squnion>Y"
    by (simp add: Sup_map_sampler Y chain_Y' compatible_sampler_of_ptree 
                  ptree_chain_imp_compatible sampler_of_ptree_Sup)
  finally show ?thesis .
qed


lemma (in ccpo) continuous_map_fixp_le_fixp:
  fixes f :: "'a \<Rightarrow> 'a" and g :: "'b \<Rightarrow> 'b"
  fixes le' :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) and Sup' :: "'b set \<Rightarrow> 'b"
  assumes "class.ccpo Sup' (\<sqsubseteq>) lt'"
  assumes "monotone (\<le>) (\<le>) f" "monotone (\<sqsubseteq>) (\<sqsubseteq>) g" "mcont Sup (\<le>) Sup' (\<sqsubseteq>) h"
  assumes "\<And>x. h (f x) \<sqsubseteq> g (h x)" and "g y \<sqsubseteq> y" and "h (Sup {}) \<sqsubseteq> y"
  shows   "h (ccpo_class.fixp f) \<sqsubseteq> y"
proof -
  interpret ccpo': ccpo Sup' le' lt' by fact
  show ?thesis
  proof (induction f rule: fixp_induct)
    show "ccpo.admissible Sup (\<le>) (\<lambda>a. le' (h a) y)"
    proof (rule ccpo.admissibleI)
      fix A assume A: "Complete_Partial_Order.chain (\<le>) A" "A \<noteq> {}" "\<forall>x\<in>A. le' (h x) y"
      have cont: "cont Sup (\<le>) Sup' (\<sqsubseteq>) h" and mono: "monotone (\<le>) (\<sqsubseteq>) h"
        using \<open>mcont _ _ _ _ h\<close> unfolding mcont_def by auto
      have "h (Sup A) = Sup' (h ` A)"
        by (intro contD[OF cont]) (use A in auto)
      also from A have "\<dots> \<sqsubseteq> y"
        by (intro ccpo'.ccpo_Sup_least chain_imageI[of "(\<le>)"] monotoneD[OF mono]) auto
      finally show "h (\<Squnion> A) \<sqsubseteq> y" .
    qed
  next
    fix x :: 'a
    assume "h x \<sqsubseteq> y"
    thus "h (f x) \<sqsubseteq> y"
      by (metis assms(3,5,6) ccpo'.order.trans monotoneD)
  qed fact+
qed

text \<open>
  A less general, simplified version of the above:

  Let \<open>f :: 'a \<Rightarrow> 'a\<close>, \<open>g :: 'b \<Rightarrow> 'b\<close>, and \<open>h :: 'a \<Rightarrow> 'b\<close> be monotone functions satisfying
  \<open>h \<circ> f = g \<circ> h\<close>. Furthermore assume that \<open>h\<close> is continuous and \<open>h(\<bottom>) = \<bottom>\<close>.
  Then the least fixed point of \<open>g\<close> is equal to the least fixed point of \<open>f\<close>.
\<close>
lemma (in ccpo) continuous_map_fixp_eq_fixp:
  fixes f :: "'a \<Rightarrow> 'a" and g :: "'b \<Rightarrow> 'b"
  fixes le' :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) and Sup' :: "'b set \<Rightarrow> 'b"
  assumes "class.ccpo Sup' (\<sqsubseteq>) lt'"
  assumes "monotone (\<le>) (\<le>) f" and "monotone (\<sqsubseteq>) (\<sqsubseteq>) g" "mcont Sup (\<le>) Sup' (\<sqsubseteq>) h"
  assumes "\<And>x. h (f x) = g (h x)" and "h (Sup {}) = Sup' {}"
  shows   "h (ccpo_class.fixp f) = ccpo.fixp Sup' (\<sqsubseteq>) g"
proof -
  interpret ccpo': ccpo Sup' le' lt' by fact
  show ?thesis
  proof (rule ccpo'.order.antisym)
    show "h (ccpo_class.fixp f) \<sqsubseteq> ccpo.fixp Sup' (\<sqsubseteq>) g"
    proof (rule continuous_map_fixp_le_fixp[OF assms(1-4)])
      show "h (f x) \<sqsubseteq> g (h x)" for x using assms(5)
        by simp
      show "g (ccpo.fixp Sup' (\<sqsubseteq>) g) \<sqsubseteq> ccpo.fixp Sup' (\<sqsubseteq>) g"
        using \<open>monotone _ _ g\<close> ccpo'.order.eq_iff ccpo'.fixp_unfold by blast
      show "h (\<Squnion> {}) \<sqsubseteq> ccpo'.fixp g"
        using \<open>h (Sup {}) = _\<close> by (simp add: ccpo'.ccpo_Sup_below_iff chain_empty)
    qed
    show "ccpo.fixp Sup' (\<sqsubseteq>) g \<sqsubseteq> h (ccpo_class.fixp f)"
      by (metis assms(2,3,5) ccpo'.fixp_lowerbound ccpo'.order.refl fixp_unfold)
  qed
qed



lemma partial_function_definitions_sampler: 
  "partial_function_definitions (\<le>) (Sup :: 'a sampler set \<Rightarrow> _)"
  by standard (auto simp: ccpo_Sup_upper ccpo_Sup_least)
  
interpretation sampler: partial_function_definitions "(\<le>)" "Sup :: 'a sampler set \<Rightarrow> _"
  rewrites "Sup {} \<equiv> (bot :: 'a sampler)" 
  by (rule partial_function_definitions_sampler) auto

declaration \<open>Partial_Function.init "sampler" \<^term>\<open>sampler.fixp_fun\<close>
  \<^term>\<open>sampler.mono_body\<close> @{thm sampler.fixp_rule_uc} @{thm sampler.fixp_induct_uc} NONE\<close>


consts coin_sampler :: "real \<Rightarrow> bool sampler"


abbreviation "mono_sampler \<equiv> monotone (fun_ord ((\<le>) :: 'a sampler \<Rightarrow> _)) ((\<le>) :: 'b sampler \<Rightarrow> _)"

lemma map_sampler_mono' [partial_function_mono]: 
  "mono_sampler B \<Longrightarrow> mono_sampler (\<lambda>g. map_sampler f (B g))"
  by (auto simp: monotone_def fun_ord_def intro: map_sampler_mono)

lemma bind_sampler_mono' [partial_function_mono]:
  assumes mf: "mono_sampler B" and mg: "\<And>y. mono_sampler (\<lambda>f. C y f)"
  shows "mono_sampler (\<lambda>f. bind_sampler (B f) (\<lambda>y. C y f))"
  using assms by (auto simp: monotone_def fun_ord_def intro: bind_sampler_mono)


declare [[function_internals]]

partial_function (spmf) foo :: "real \<Rightarrow> nat spmf"
  where "foo p = do {b \<leftarrow> spmf_of_pmf (bernoulli_pmf p); if b then return_spmf 0 else map_spmf Suc (foo (p / 2))}"
print_theorems

partial_function (sampler) foos :: "real \<Rightarrow> nat sampler"
  where "foos p = do {b \<leftarrow> coin_sampler p; if b then return_sampler 0 else map_sampler Suc (foos (p / 2))}"
print_theorems

thm foo_def foos_def


partial_function (spmf) bar :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat spmf"
  where "bar p q r = do {b \<leftarrow> spmf_of_pmf (bernoulli_pmf (p + q + r)); if b then return_spmf 0 else map_spmf Suc (bar p q r)}"
print_theorems
partial_function (sampler) bars :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat sampler"
  where "bars p q r = do {b \<leftarrow> coin_sampler (p + q + r); if b then return_sampler 0 else map_sampler Suc (bars p q r)}"
print_theorems
thm bar_def bars_def


definition rel_spmf_sampler :: "'a spmf \<Rightarrow> 'a sampler \<Rightarrow> bool" where
  "rel_spmf_sampler q p \<longleftrightarrow> q = spmf_of_sampler p"

lemma admissible_rel_sampler:
  "ccpo.admissible (prod_lub lub_spmf Sup) (rel_prod (ord_spmf (=)) (\<le>)) (case_prod rel_spmf_sampler)"
  (is "ccpo.admissible ?lub ?ord ?P")
proof (rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ?ord Y"
    and Y: "Y \<noteq> {}"
    and R: "\<forall>(p, q) \<in> Y. rel_spmf_sampler p q"
  from R have R: "\<And>p q. (p, q) \<in> Y \<Longrightarrow> rel_spmf_sampler p q" by auto
  have chain1: "Complete_Partial_Order.chain (ord_spmf (=)) (fst ` Y)"
    and chain2: "Complete_Partial_Order.chain (\<le>) (snd ` Y)"
    using chain by(rule chain_imageI; clarsimp)+
  from Y have Y1: "fst ` Y \<noteq> {}" and Y2: "snd ` Y \<noteq> {}" by auto
 
  have "lub_spmf (fst ` Y) = lub_spmf (spmf_of_sampler ` snd ` Y)"
    unfolding image_image using R
    by (intro arg_cong[of _ _ lub_spmf] image_cong) (auto simp: rel_spmf_sampler_def)
  also have "\<dots> = spmf_of_sampler (\<Squnion>(snd ` Y))"
    by (rule lub_spmf_of_sampler chain2)+
  finally have "rel_spmf_sampler (lub_spmf (fst ` Y)) (Sup (snd ` Y))"
    unfolding rel_spmf_sampler_def .
  then show "?P (?lub Y)"
    by (simp add: prod_lub_def)
qed

lemma admissible_rel_spmf_sampler [cont_intro]:
  "\<lbrakk> mcont lub ord lub_spmf (ord_spmf (=)) f;
     mcont lub ord Sup (\<le>) g \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. rel_spmf_sampler (f x) (g x))"
  by (rule admissible_subst[OF admissible_rel_sampler, where f="\<lambda>x. (f x, g x)", simplified]) 
     (rule mcont_Pair)

lemma mcont2mcont_spmf_of_sampler[THEN spmf.mcont2mcont, cont_intro]:
  shows mcont_spmf_of_sampler: "mcont Sup (\<le>) lub_spmf (ord_spmf (=)) spmf_of_sampler"
  unfolding mcont_def monotone_def cont_def
  by (auto simp: spmf_of_sampler_mono lub_spmf_of_sampler)




lemma (in ccpo) ccpo: "class.ccpo Sup (\<le>) (mk_less (\<le>))"
proof -
  have "class.ccpo Sup (\<le>) ((<) :: 'a \<Rightarrow> _)"
    by (rule ccpo_axioms)
  also have "((<) :: 'a \<Rightarrow> _) = mk_less (\<le>)"
    by (auto simp: fun_eq_iff mk_less_def)
  finally show ?thesis .
qed

context includes lifting_syntax
begin

lemma fixp_sampler_parametric:
  assumes f: "\<And>x. mono_spmf (\<lambda>f. F f x)"
  and g: "\<And>x. mono_sampler (\<lambda>f. G f x)"
  and param: "((A ===> rel_spmf_sampler) ===> A ===> rel_spmf_sampler) F G"
  shows "(A ===> rel_spmf_sampler) (spmf.fixp_fun F) (sampler.fixp_fun G)"
using f g
proof(rule parallel_fixp_induct_1_1[OF partial_function_definitions_spmf partial_function_definitions_sampler _ _ reflexive reflexive, where P="(A ===> rel_spmf_sampler)"])
  show "ccpo.admissible (prod_lub (fun_lub lub_spmf) (fun_lub Sup)) (rel_prod (fun_ord (ord_spmf (=))) (fun_ord (\<le>))) (\<lambda>x. (A ===> rel_spmf_sampler) (fst x) (snd x))"
    unfolding rel_fun_def
    by(rule admissible_all admissible_imp cont_intro)+
  show "(A ===> rel_spmf_sampler) (\<lambda>_. lub_spmf {}) (\<lambda>_. Sup {})"
    by (auto simp: rel_fun_def rel_spmf_sampler_def)
  show "(A ===> rel_spmf_sampler) (F f) (G g)" if "(A ===> rel_spmf_sampler) f g" for f g
    using that by(rule rel_funD[OF param])
qed

definition lossless_sampler :: "'a sampler \<Rightarrow> bool"
  where "lossless_sampler p = lossless_spmf (spmf_of_sampler p)"

lemma ord_spmf_losslessD:
  assumes "ord_spmf (=) p q" "lossless_spmf p"
  shows   "p = q"
proof -
  have "rel_pmf (=) p q"
    using assms(2)
    by (intro pmf.rel_mono_strong[OF assms(1)])
       (auto simp: ord_option_case lossless_iff_set_pmf_None split: option.splits)
  thus ?thesis
    by (simp add: pmf.rel_eq)
qed

lemma fixp_sampler_parametric':
  assumes f: "\<And>x. mono_spmf (\<lambda>f. F f x)"
  and g: "\<And>x. mono_sampler (\<lambda>f. G f x)"
  and param: "((A ===> rel_spmf_sampler) ===> A ===> rel_spmf_sampler) F G"
  and fp: "F h = h"
  and lossless: "lossless_sampler (sampler.fixp_fun G y)"
  and rel: "A x y"
  shows "rel_spmf_sampler (h x) (sampler.fixp_fun G y)"
proof -
  have "(A ===> rel_spmf_sampler) (spmf.fixp_fun F) (sampler.fixp_fun G)"
    by (rule fixp_sampler_parametric[OF f g param])
  with rel have "rel_spmf_sampler (spmf.fixp_fun F x) (sampler.fixp_fun G y)"
    by (auto dest: rel_funD)
  hence eq: "spmf.fixp_fun F x = spmf_of_sampler (sampler.fixp_fun G y)"
    by (auto simp: rel_spmf_sampler_def)

  have le: "ord_spmf (=) (spmf.fixp_fun F x) (h x)"
  proof (induction F arbitrary: x rule: ccpo.fixp_induct[OF spmf.ccpo])
    show "spmf.admissible (\<lambda>a. \<forall>x. ord_spmf (=) (a x) (h x))"
      by (rule cont_intro)+
  next
    show "monotone spmf.le_fun spmf.le_fun F"
      using f monotone_fun_ord_apply by blast
  next
    show "ord_spmf (=) (spmf.lub_fun {} x) (h x)" for x
      by simp
  next
    fix F' :: "'a \<Rightarrow> 'b spmf" and x :: 'a
    assume *: "\<And>x. ord_spmf (=) (F' x) (h x)"
    have "ord_spmf (=) (F F' x) (F h x)"     
      using f * unfolding monotone_def fun_ord_def by blast
    thus "ord_spmf (=) (F F' x) (h x)"
      by (simp add: fp)
  qed
  have "spmf.fixp_fun F x = h x"
    using ord_spmf_losslessD[OF le] lossless
    by (auto simp: eq lossless_sampler_def)
  thus "rel_spmf_sampler (h x) (sampler.fixp_fun G y)"
    by (simp add: rel_spmf_sampler_def eq)
qed

lemma fixp_sampler_parametric'':
  assumes f: "\<And>x. mono_spmf (\<lambda>f. F f x)"
  and g: "\<And>x. mono_sampler (\<lambda>f. G f x)"
  and param: "((A ===> rel_spmf_sampler) ===> A ===> rel_spmf_sampler) F G"
  and fp: "F h = h"
  and lossless: "\<And>x. lossless_sampler (sampler.fixp_fun G x)"
  shows "(A ===> rel_spmf_sampler) h (sampler.fixp_fun G)"
  unfolding rel_fun_def
  using fixp_sampler_parametric'[OF f g param fp lossless] by blast


lemma rel_sampler_bot [transfer_rule]:
  "rel_spmf_sampler (return_pmf None) bot"
  by (auto simp: rel_spmf_sampler_def)

lemma rel_sampler_return [transfer_rule]:
  "((=) ===> rel_spmf_sampler) return_spmf return_sampler"
  by (auto simp: rel_spmf_sampler_def rel_fun_def)

lemma rel_sampler_bind [transfer_rule]:
  "(rel_spmf_sampler ===> ((=) ===> rel_spmf_sampler) ===> rel_spmf_sampler) bind_spmf bind_sampler"
  by (auto simp: rel_spmf_sampler_def rel_fun_def intro: bind_spmf_cong)

lemma rel_sampler_map [transfer_rule]:
  "(((=) ===> (=)) ===> rel_spmf_sampler ===> rel_spmf_sampler) map_spmf map_sampler"
  by (auto simp: rel_spmf_sampler_def rel_fun_def intro: map_spmf_cong)

lemma rel_sampler_coin [transfer_rule]:
  "((=) ===> rel_spmf_sampler) (\<lambda>p. spmf_of_pmf (bernoulli_pmf p)) coin_sampler"
  sorry


lemma "((=) ===> rel_spmf_sampler) foo foos"
  unfolding foos_def foo_def
  apply (rule fixp_sampler_parametric)
    apply (rule foo.mono)
     apply (rule foos.mono)
  apply transfer_prover
  done

lemma "((=) ===> (=) ===> (=) ===> rel_spmf_sampler) bar bars"
  unfolding bar_def bars_def
  apply (rule rel_funD[OF curry_transfer])
  apply (rule rel_funD[OF curry_transfer])
  apply (rule fixp_sampler_parametric)
    apply (rule bar.mono)
     apply (rule bars.mono)
  apply transfer_prover
  done


lemma "rel_spmf_sampler (foo p) (foos p)"
  unfolding foos_def foo_def
  apply (rule rel_funD[rotated, of "(=)", OF refl fixp_sampler_parametric])
    apply (rule foo.mono)
     apply (rule foos.mono)
  apply transfer_prover
  done




abbreviation bot_spmf where "bot_spmf \<equiv> return_pmf None"

definition assert_spmf' where "assert_spmf' b = return_pmf (if b then Some undefined else None)"

lemma pmf_assert_spmf'_None [simp]: "pmf (assert_spmf' b) None = (if b then 0 else 1)"
  by (auto simp: assert_spmf'_def)

lemma assert_spmf'_True: "assert_spmf' True = return_spmf undefined"
  by (auto simp: assert_spmf'_def)

lemma assert_spmf'_False: "assert_spmf' False = bot_spmf"
  by (auto simp: assert_spmf'_def)

lemma lossless_assert_spmf'_iff [simp]: "lossless_spmf (assert_spmf' b) \<longleftrightarrow> b"
  by (auto simp: assert_spmf'_def)




declare [[function_internals]]

partial_function (spmf) f :: "real \<Rightarrow> bool spmf" where
 "f p = do {b \<leftarrow> spmf_of_pmf (pmf_of_set UNIV); if b then return_spmf (p \<ge> 1/2) else f (if p < 1/2 then 2*p else 2*p-1)}"

thm f.simps
thm f_def

lemmas [simp del] = spmf_of_pmf_pmf_of_set

definition F :: "(real \<Rightarrow> bool spmf) \<Rightarrow> real \<Rightarrow> bool spmf" where
  "F = (\<lambda>f p. spmf_of_pmf (pmf_of_set UNIV) \<bind> (\<lambda>b. if b then return_spmf (1 / 2 \<le> p)
                else f (if p < 1 / 2 then 2 * p else 2 * p - 1)))"

lemma "f = spmf.fixp_fun F"
  by (simp add: f_def F_def)

lemma "pmf (F (\<lambda>_. bot_spmf) p) None = 1 / 2"
  unfolding F_def
  apply (simp add: pmf_bind_spmf_None pmf_bind integral_pmf_of_set UNIV_bool)
  done

lemma "p \<in> {0..1} \<Longrightarrow> lossless_spmf (F (\<lambda>p. assert_spmf' (p \<in> {0..1})) p)"
  unfolding F_def
  by simp




partial_function (spmf) g :: "real \<Rightarrow> nat spmf" where
  "g p = do {
     b \<leftarrow> spmf_of_pmf (bernoulli_pmf p);
     if b then return_spmf 0 else map_spmf ((+) 1) (g p)
  }"

thm g.simps
thm g_def

lemmas [simp del] = spmf_of_pmf_pmf_of_set

definition G :: "(real \<Rightarrow> nat spmf) \<Rightarrow> real \<Rightarrow> nat spmf" where
  "G = (\<lambda>g p. spmf_of_pmf (bernoulli_pmf p) \<bind>
         (\<lambda>b. if b then return_spmf 0 else map_spmf ((+) 1) (g p)))"

lemma "p \<in> {0..1} \<Longrightarrow> pmf (G (\<lambda>_. bot_spmf) p) None = 1 - p"
  unfolding G_def
  apply (simp add: pmf_bind_spmf_None pmf_bind integral_pmf_of_set UNIV_bool)
  done


lemma "p \<in> {0..<1} \<Longrightarrow> pmf (G (\<lambda>p. assert_spmf' (p \<in> {0..<1})) p) None = 0"
  unfolding G_def
  apply (simp add: pmf_bind_spmf_None pmf_bind integral_pmf_of_set UNIV_bool pmf_map)
  apply (simp add: assert_spmf'_True assert_spmf'_False)
  done

lemma "p \<in> {0..<1} \<Longrightarrow> lossless_spmf (G (\<lambda>p. assert_spmf' (p \<in> {0..<1})) p)"
  unfolding G_def by simp



context
  fixes n :: nat
begin

partial_function (spmf) h :: "nat \<Rightarrow> nat \<Rightarrow> nat spmf"
where
  "h v c = 
  (if v \<ge> n then if c < n then return_spmf c else h (v - n) (c - n)
   else do {
     b \<leftarrow> spmf_of_pmf (pmf_of_set (UNIV :: bool set));
     h (2 * v) (2 * c + (if b then 1 else 0)) } )"

thm h_def

definition H where "H =
 ((\<lambda>h (v, c).
       if n \<le> v then if c < n then return_spmf c else curry h (v - n) (c - n)
       else spmf_of_pmf (pmf_of_set UNIV) \<bind>
            (\<lambda>b. curry h (2 * v) (2 * c + (if b then 1 else 0)))))"


lemma "c < v \<Longrightarrow> pmf (H (\<lambda>_. bot_spmf) (v, c)) None = (if v \<ge> n \<and> c < n then 0 else 1)"
  unfolding H_def
  apply (simp add: pmf_bind_spmf_None pmf_bind integral_pmf_of_set UNIV_bool)
  done


lemma "c < v \<Longrightarrow> lossless_spmf (H (\<lambda>(v,c). assert_spmf' (c < v)) (v, c))"
  unfolding H_def
  apply (simp add: pmf_bind_spmf_None pmf_bind integral_pmf_of_set UNIV_bool pmf_map)
  apply linarith
  done


function aux :: "nat \<Rightarrow> nat" where "aux v = (if v \<ge> n \<or> v = 0 then 0 else aux (2 * v) + 1)"
  by auto
termination
  by (relation "Wellfounded.measure ((\<lambda>v. n - v))") auto

definition l where "l = Discrete.log n + 1"

definition m_H :: "nat \<times> nat \<Rightarrow> real"
  where "m_H = (\<lambda>(v,c). let k = aux v in (2^k-(n-c*2^k)) / 2^k)"

definition m_H' :: "nat \<times> nat \<Rightarrow> nat"
  where "m_H' = (\<lambda>(v,c). let k = aux v in if c * 2^k \<ge> n then 1 else 0)"

partial_function (spmf) j :: "nat \<Rightarrow> nat \<Rightarrow> bool spmf"
  where "j v c = (if v \<ge> n then return_spmf (c \<ge> n) else spmf_of_set {True,False} \<bind> (\<lambda>b. j (2 * v) (2*c + of_bool b)))"

definition R_H where
  "R_H = (\<lambda>(v,c) (v',c').  m_H (v',c') < m_H (v, c) \<or>
             (m_H (v',c') = m_H (v, c) \<and> v' < v))"

(*lemma "pmf (map_pmf (\<lambda>b. m_H (2 * v, 2 * c + of_bool b) *)

definition step 
  where "step = (\<lambda>(v,c). map_pmf (\<lambda>b. (2 * v, 2 * c + of_bool b)) (pmf_of_set {True, False}))"

end

value "m_H 10 (4, 1)"
value "m_H 10 (13, 5)"

lemmas [code] = j.simps

  

value "spmf (j 10 2 0) True"
value "m_H 10 (1, 0)"
value "m_H 10 (2, 0)"
value "m_H 10 (2, 1)"

value "m_H 10 (1, 0)"
value "m_H 10 (2, 1)"
value "m_H 10 (4, 3)"
value "m_H 10 (8, 7)"
value "m_H 10 (16, 15)"

value " (\<Union>n\<in>{10..10}. \<Union>v\<in>{1..<n}. \<Union>c\<in>{0..<v}. 
let p = measure_pmf.expectation (step (v,c)) (\<lambda>vc'. m_H n vc' - m_H n (v,c)) in {p})"

value " (\<Union>n\<in>{1..10}. \<Union>v\<in>{1..<n}. \<Union>c\<in>{0..<v}. 
let p = pmf (map_pmf (\<lambda>vc'. m_H n vc' < m_H n (v,c)) (step (v,c))) True in if p = 0 then {(n,v,c)} else {})"

value " (\<Union>n\<in>{1..10}. \<Union>v\<in>{1..<n}. \<Union>c\<in>{0..<v}. 
let p = pmf (map_pmf (\<lambda>vc'. R_H n (v,c) vc') (step (v,c))) True in if p = 0 then {(n,v,c)} else {})"

value "(\<Union>n\<in>{10..10}. \<Union>v\<in>{n..<2*n}. \<Union>c\<in>{n..<v}. if m_H n (v,c) \<le> m_H n (v-n, c-n) then {(n,v,c)} else {})"
value "(\<Union>n\<in>{10..10}. \<Union>v\<in>{n..<2*n}. \<Union>c\<in>{n..<v}. {m_H n (v-n, c-n)})"


value "let n = 10; v = 13 in map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. m_H n vc' > m_H n (v,c)) (step (v,c))) True) [0..<v]"

value "let n = 10; v = 8 in map (\<lambda>c. m_H n (v,c)) [0..<v]"
value "let n = 10; v = 8 in map (\<lambda>c. spmf (j n v c) True * 16) [0..<v]"

value "let n = 65; v = 16 in map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. m_H n vc' < m_H n (v,c)) (step (v,c))) True) [0..<v]"
value "let n = 65; v = 32 in map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. m_H n vc' < m_H n (v,c)) (step (v,c))) True) [0..<v]"
value "let n = 65; v = 64 in map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. m_H n vc' < m_H n (v,c)) (step (v,c))) True) [0..<v]"

value "let n = 65; v = 16 in map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. R_H n vc' (v,c)) (step (v,c))) True) [0..<v]"
value "let n = 65; v = 32 in map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. R_H n vc' (v,c)) (step (v,c))) True) [0..<v]"
value "let n = 65; v = 64 in map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. R_H n vc' (v,c)) (step (v,c))) True) [0..<v]"
value "let n = 65; v = 128 in map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. R_H n vc' (v,c)) (step (v,c))) True) [0..<v]"


value "let n = 65 in list_all (\<lambda>v. list_all (\<lambda>c. pmf (map_pmf (\<lambda>vc'. R_H n (v,c) vc') (step (v,c))) True > 0) [0..<v]) [1..<2*n]"
value "let n = 65 in foldl min 1 (map (\<lambda>v. foldl min 1 (map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. R_H n (v,c) vc') (step (v,c))) True) [0..<v])) [1..<2*n])"
value "let n = 65 in foldl min 1 (map (\<lambda>v. foldl min 1 (map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. R_H n (v,c) vc') (step (v,c))) True) [0..<v])) [1..<2*n])"
value "let n = 65 in foldl max 0 (map (\<lambda>v. foldl max 0 (map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. vc' = (v,c)) (step (v,c))) True) [0..<v])) [1..<2*n])"

value "let n = 65 in filter (Not o ((=) []) o snd) (map (\<lambda>v. (v, filter (\<lambda>c. pmf (map_pmf (\<lambda>vc'. vc' = (v,c)) (step (v,c))) True > 0) [0..<v])) [1..<2*n])"

value "let n = 10; v = 8 in map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. m_H n vc' < m_H n (v,c)) (step (v,c))) True) [0..<v]"
value "let n = 10; v = 4 in map (\<lambda>c. pmf (map_pmf (\<lambda>vc'. m_H n vc' < m_H n (v,c)) (step (v,c))) True) [0..<v]"
value "let n = 10; v = 16 in map (\<lambda>c. m_H n (v - n, c - n) < m_H n (v, c)) [n..<v]"
value "let n = 65; v = 128 in map (\<lambda>c. m_H n (v - n, c - n) < m_H n (v, c)) [n..<v]"

value "let n = 65; v = 128 in map (\<lambda>c. int (m_H n (v, c)) - int (m_H n (v - n, c - n))) [n..<v]"
value "let n = 65; v = 128 in map (\<lambda>c.  (m_H n (v, c)) ) [n..<v]"
value "let n = 65; v = 128 in map (\<lambda>c.  (m_H n (v - n, c - n))) [n..<v]"
value "let n = 65; v = 128 in map (\<lambda>c.  (R_H n (v,c) (v - n, c - n))) [n..<v]"


lemma "c < v \<Longrightarrow> v < n \<or> c \<ge> n \<Longrightarrow>
         lossless_spmf (H (\<lambda>(v',c'). assert_spmf' (n - v' < n - v)) (v, c))"
  unfolding H_def
  apply (simp add: pmf_bind_spmf_None pmf_bind integral_pmf_of_set UNIV_bool pmf_map)
  apply (auto simp: not_le not_less)
  
  apply linarith
  done




lemma "rel_fun (=) rel_spmf_sampler1 foos foo"
  apply (induction rule: foos.fixp_induct)
    apply (rule cont_intro)+
   apply simp
  apply (subst foo.simps)
  sorry

lemma "rel_spmf_sampler2 (foos p) (foo p)"
  apply (induction rule: foo.fixp_induct)
    apply (rule cont_intro)+
   apply simp
  apply (subst foos.simps)
  sorry


lemma "rel_spmf_sampler (foos p) (foo p)"
  apply (induction 

lemma
  fixes f :: "('a \<Rightarrow> 'b sampler) \<Rightarrow> 'a \<Rightarrow> 'b sampler"
  fixes g :: "('a \<Rightarrow> 'b spmf) \<Rightarrow> 'a \<Rightarrow> 'b spmf"
  assumes "monotone sampler.le_fun (\<le>) f" 
  assumes "\<And>x. monotone spmf.le_fun (ord_spmf (=)) (\<lambda>g'. g g' x)"
  assumes "rel_fun (rel_fun (=) rel_spmf_sampler) (rel_fun (=) rel_spmf_sampler) f g"
  shows   "rel_fun (=) rel_spmf_sampler (sampler.fixp_fun f) (spmf.fixp_fun g)"
proof (intro rel_funI; clarify)
  fix x :: 'a



  have "spmf.fixp_fun g x = spmf_of_sampler (sampler.fixp_fun f x)"
    unfolding ccpo.fixp_def [OF spmf.ccpo] ccpo.fixp_def [OF sampler.ccpo]

    ML_val \<open>@{term "sampler.lub_fun"}\<close>
    term lub_spmf
    

    unfolding fun_lub_def
    apply (subst lub_spmf_of_sampler [symmetric])
    
    find_theorems "Complete_Partial_Order.chain" ccpo.iterates

    ML_val \<open>@{term "spmf.lub_fun"}\<close>
    find_theorems "spmf.lub_fun"
    

  thus "rel_spmf_sampler (sampler.fixp_fun f x) (spmf.fixp_fun g x)"
    unfolding rel_spmf_sampler_def .



lemma foo:
  fixes f :: "'a sampler \<Rightarrow> 'a sampler" and g :: "'a spmf \<Rightarrow> 'a spmf"
  assumes "mono f" "monotone (ord_spmf (=)) (ord_spmf (=)) g"
  assumes "\<And>x. ord_spmf (=) (spmf_of_sampler (f x)) (g (spmf_of_sampler x))"
  assumes "ord_spmf (=) (g y) y"
  shows   "ord_spmf (=) (spmf_of_sampler (ccpo_class.fixp f)) y"
proof (rule continuous_map_fixp_le_fixp[OF ccpo_spmf assms(1,2) _ _ assms(4)])
  show "ord_spmf (=) (spmf_of_sampler (f x)) (g (spmf_of_sampler x))" for x
    using assms(3)[of x] .
  show "mcont Sup (\<le>) lub_spmf (ord_spmf (=)) spmf_of_sampler"
    by (auto simp: mcont_def monotone_def cont_def spmf_of_sampler_mono lub_spmf_of_sampler)
qed auto

definition lossless_sampler :: "'a sampler \<Rightarrow> bool"
  where "lossless_sampler p = lossless_spmf (spmf_of_sampler p)"

lemma ord_spmf_lossless:
  assumes "ord_spmf (=) p q" "lossless_spmf p"
  shows   "p = q"
proof -
  have "rel_pmf (=) p q"
    using assms(2)
    by (intro pmf.rel_mono_strong[OF assms(1)])
       (auto simp: ord_option_case lossless_iff_set_pmf_None split: option.splits)
  thus ?thesis
    by (simp add: pmf.rel_eq)
qed

lemma foo1:
  fixes f :: "'a sampler \<Rightarrow> 'a sampler" and g :: "'a spmf \<Rightarrow> 'a spmf"
  assumes "mono f" "monotone (ord_spmf (=)) (ord_spmf (=)) g"
  assumes "\<And>x. spmf_of_sampler (f x) = g (spmf_of_sampler x)"
  assumes "g y = y"
  assumes "lossless_sampler (ccpo_class.fixp f)"
  shows   "spmf_of_sampler (ccpo_class.fixp f) = y"
proof -
  have "ord_spmf (=) (spmf_of_sampler (ccpo_class.fixp f)) y"
    by (rule foo) (use assms in auto)
  with assms(5) show ?thesis
    unfolding lossless_sampler_def using ord_spmf_lossless by blast
qed

definition rel_spmf_sampler :: "'a sampler \<Rightarrow> 'a spmf \<Rightarrow> bool" where
  "rel_spmf_sampler p q \<longleftrightarrow> q = spmf_of_sampler p"

definition rel_pmf_sampler :: "'a sampler \<Rightarrow> 'a pmf \<Rightarrow> bool" where
  "rel_pmf_sampler p q \<longleftrightarrow> spmf_of_pmf q = spmf_of_sampler p"

lemma foo2:
  fixes f :: "'a sampler \<Rightarrow> 'a sampler" and g :: "'a spmf \<Rightarrow> 'a spmf"
  assumes "mono f" "monotone (ord_spmf (=)) (ord_spmf (=)) g"
  assumes "rel_fun rel_spmf_sampler rel_spmf_sampler f g"
  assumes "g y = y"
  assumes "lossless_sampler (ccpo_class.fixp f)"
  shows   "spmf_of_sampler (ccpo_class.fixp f) = y"
proof -
  have "ord_spmf (=) (spmf_of_sampler (ccpo_class.fixp f)) y"
    by (rule foo) (use assms in \<open>auto simp: rel_spmf_sampler_def rel_fun_def\<close>)
  with assms(5) show ?thesis
    unfolding lossless_sampler_def using ord_spmf_lossless by blast
qed


declare [[function_internals]]

partial_function (spmf) foo :: "real \<Rightarrow> nat spmf"
  where "foo p = do {b \<leftarrow> spmf_of_pmf (bernoulli_pmf p); if b then return_spmf 0 else map_spmf Suc (foo p)}"

partial_function (spmf) bar :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat spmf"
  where "bar p q r = do {b \<leftarrow> spmf_of_pmf (bernoulli_pmf (p + q + r)); if b then return_spmf 0 else map_spmf Suc (bar p q r)}"

thm bar_def


thm foo_def[unfolded fun_lub_def]
ML_val \<open>@{thm foo_def} |> Thm.concl_of\<close>

















context
begin

interpretation pmf_as_measure .

lift_definition spmf_of_sampler :: "'a sampler \<Rightarrow> 'a spmf" is "measure_sampler"
proof goal_cases
  case (1 r)
  define M where "M = measure_sampler r"
  have "coin_space.random_variable (count_space UNIV) (map_option fst \<circ> run_sampler r)"
    by measurable
  then interpret M: prob_space M
    by (auto simp: M_def measure_sampler_def intro!: coin_space.prob_space_distr prob_space_return)
  show ?case
    unfolding M_def [symmetric]
  proof (intro conjI)
    show "prob_space M"
      by (fact M.prob_space_axioms)
  next
    show "sets M = UNIV"
      by (simp add: M_def measure_sampler_def)
  next
    have meas: "coin_space.random_variable (count_space UNIV) (map_option fst \<circ> run_sampler r)"
      by measurable
    show "AE x in M. Sigma_Algebra.measure M {x} \<noteq> 0"
    proof (subst M.AE_support_countable)
      have "AE x in coin_space. map_option fst (run_sampler r x) \<in> options (range_sampler r)"
        by (intro always_eventually)
           (auto simp: options_def map_option_case intro: imageI in_range_samplerI split: option.splits)
      hence "AE x in M. x \<in> options (range_sampler r)"
        unfolding M_def measure_sampler_def using meas by (simp add: AE_distr_iff)
      thus "\<exists>S. countable S \<and> (AE x in M. x \<in> S)"
        by (intro exI[of _ "options (range_sampler r)"]) (use countable_range_pmfsr in auto)
    qed (auto simp: M_def measure_sampler_def)
  qed
qed

lemma spmf_of_sampler_map:
  "spmf_of_sampler (map_sampler f p) = map_spmf f (spmf_of_sampler p)"
  apply (transfer fixing: f)
  apply (simp add: measure_sampler_def distr_distr)
  apply (simp add: o_def option.map_comp)
  done







definition map_pmfsr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pmfsr \<Rightarrow> 'b pmfsr" where
  "map_pmfsr f r bs = map_option (map_prod f id) (r bs)"




(*
definition wf_pmfsr :: "'a pmfsr \<Rightarrow> bool" where
  "wf_pmfsr r \<longleftrightarrow>
     r \<in> coin_space \<rightarrow>\<^sub>M count_space UNIV \<and>
     countable (range_pmfsr r) \<and>
     wf_pmfsr r"
*)






definition return_pmfsr :: "'a \<Rightarrow> 'a pmfsr" where
  "return_pmfsr x bs = Some (x, 0)"

definition coin_pmfsr :: "bool pmfsr" where
  "coin_pmfsr bs = Some (shd bs, 1)"

definition bind_pmfsr :: "'a pmfsr \<Rightarrow> ('a \<Rightarrow> 'b pmfsr) \<Rightarrow> 'b pmfsr" where
  "bind_pmfsr r f bs =
     do {(x, m) \<leftarrow> r bs; (y, n) \<leftarrow> f x (sdrop m bs); Some (y, m + n)}"

definition consumption_pmfsr :: "'a pmfsr \<Rightarrow> nat pmfsr" where
  "consumption_pmfsr r bs = map_option (\<lambda>(_, n). (n, n)) (r bs)"


adhoc_overloading Monad_Syntax.bind bind_pmfsr

lemma map_pmfsr_id [simp]: "map_pmfsr id r = r"
  by (auto simp: fun_eq_iff map_pmfsr_def return_pmfsr_def Option_bind_conv_case map_option_case
           split: option.splits)

lemma map_pmfsr_id' [simp]: "map_pmfsr (\<lambda>x. x) r = r"
  by (auto simp: fun_eq_iff map_pmfsr_def return_pmfsr_def Option_bind_conv_case map_option_case
           split: option.splits)

lemma map_pmfsr_return [simp]: "map_pmfsr f (return_pmfsr x) = return_pmfsr (f x)"
  by (auto simp: map_pmfsr_def return_pmfsr_def)

lemma map_pmfsr_comp: "map_pmfsr (f \<circ> g) r = map_pmfsr f (map_pmfsr g r)"
  by (auto simp: fun_eq_iff map_pmfsr_def return_pmfsr_def Option_bind_conv_case map_option_case
           split: option.splits)

lemma map_pmfsr_conv_bind_pmfsr: "map_pmfsr f r = bind_pmfsr r (\<lambda>x. return_pmfsr (f x))"
  by (auto simp: fun_eq_iff bind_pmfsr_def return_pmfsr_def map_pmfsr_def Option_bind_conv_case
           split: option.splits)

lemma bind_return_pmfsr': "bind_pmfsr r return_pmfsr = r"
  by (auto simp: fun_eq_iff bind_pmfsr_def return_pmfsr_def Option_bind_conv_case
           split: option.splits)

lemma bind_return_pmfsr: "bind_pmfsr (return_pmfsr x) r = r x"
  by (auto simp: fun_eq_iff bind_pmfsr_def return_pmfsr_def  Option_bind_conv_case
           split: option.splits)

lemma bind_assoc_pmfsr: "(A :: 'a pmfsr) \<bind> B \<bind> C = A \<bind> (\<lambda>x. B x \<bind> C)"
  by (auto simp: fun_eq_iff bind_pmfsr_def return_pmfsr_def Option_bind_conv_case
           split: option.splits)  

lemma bind_pmfsr_cong:
  "p = q \<Longrightarrow> (\<And>x. x \<in> range_pmfsr q \<Longrightarrow> f x = g x) \<Longrightarrow> bind_pmfsr p f = bind_pmfsr q g"
  by (auto simp: bind_pmfsr_def fun_eq_iff Option_bind_conv_case in_range_pmfsrI split: option.splits)


lemma range_return_pmfsr [simp]: "range_pmfsr (return_pmfsr x) = {x}"
  by (auto simp: return_pmfsr_def range_pmfsr_def)

lemma wf_return_pmfsr: "wf_pmfsr (return_pmfsr x)"
proof -
  have "fst ` Some -` range (\<lambda>bs::bool stream. Some (x, 0 :: nat)) = {x}"
    by auto
  moreover have "wf_pmfsr (return_pmfsr x)"
    by (auto simp: wf_pmfsr_def return_pmfsr_def)
  ultimately show ?thesis
    unfolding wf_pmfsr_def return_pmfsr_def[abs_def] range_pmfsr_def by auto
qed

lemma range_coin_pmfsr [simp]: "range_pmfsr coin_pmfsr = UNIV"
proof safe
  fix b :: bool
  show "b \<in> range_pmfsr coin_pmfsr"
    by (rule in_range_pmfsrI[of _ "sconst b" _ 1]) (auto simp: coin_pmfsr_def)
qed auto

lemma wf_coin_pmfsr: "wf_pmfsr coin_pmfsr"
proof -
  have "coin_space.random_variable (count_space UNIV) (\<lambda>bs. Some (shd bs, 1::nat))"
    unfolding coin_space_def by measurable
  moreover have "wf_pmfsr coin_pmfsr"
    by (auto simp: wf_pmfsr_def coin_pmfsr_def)
  ultimately show ?thesis
    unfolding wf_pmfsr_def coin_pmfsr_def range_pmfsr_def by auto
qed

lemma wf_consumption_pmfsr:
  assumes "wf_pmfsr r"
  shows   "wf_pmfsr (consumption_pmfsr r)"
proof (rule wf_pmfsrI)
  fix bs bs' x n
  assume "consumption_pmfsr r bs = Some (x, n)" "stake n bs' = stake n bs"
  thus "consumption_pmfsr r bs' = Some (x, n)"
    unfolding consumption_pmfsr_def using assms by (auto dest: wf_pmfsrD)
qed

lemma range_bind_pmfsr_subset:
  "range_pmfsr (bind_pmfsr r f) \<subseteq> (\<Union>x\<in>range_pmfsr r. range_pmfsr (f x))"
proof safe
  fix x assume "x \<in> range_pmfsr (bind_pmfsr r f)"
  then obtain bs y m n where *: "r bs = Some (y, m)" "f y (sdrop m bs) = Some (x, n)"
    by (auto simp: range_pmfsr_def bind_pmfsr_def split: Option.bind_splits)
  have "Some (y, m) \<in> range r"
    by (rule range_eqI[of _ _ bs]) (use * in auto)
  hence "y \<in> fst ` Some -` range r"
    by (intro image_eqI[of _ _ "(y, m)"]) (use * in auto)
  hence "y \<in> range_pmfsr r"
    by (auto simp: range_pmfsr_def)
  moreover have "Some (x, n) \<in> range (f y)"
    by (rule range_eqI[of _ _ "sdrop m bs"]) (use * in auto)
  hence "x \<in> fst ` Some -` range (f y)"
    by (intro image_eqI[of _ _ "(x, n)"]) auto
  hence "x \<in> range_pmfsr (f y)"
    by (auto simp: range_pmfsr_def)
  ultimately show "x \<in> (\<Union>y\<in>range_pmfsr r. range_pmfsr (f y))"
    by blast
qed

lemma range_bind_pmfsr_eq:
  assumes "wf_pmfsr r"
  shows   "range_pmfsr (bind_pmfsr r f) = (\<Union>x\<in>range_pmfsr r. range_pmfsr (f x))"
proof
  show "range_pmfsr (bind_pmfsr r f) \<subseteq> (\<Union>x\<in>range_pmfsr r. range_pmfsr (f x))"
    by (rule range_bind_pmfsr_subset)
next
  show "(\<Union>x\<in>range_pmfsr r. range_pmfsr (f x)) \<subseteq> range_pmfsr (bind_pmfsr r f)"
  proof safe
    fix y x
    assume y: "y \<in> range_pmfsr r" and x: "x \<in> range_pmfsr (f y)"
    from y obtain m bs where y': "r bs = Some (y, m)"
      unfolding range_pmfsr_def by (auto simp: eq_commute)
    from x obtain n bs' where x': "f y bs' = Some (x, n)"
      by (auto simp: range_pmfsr_def eq_commute)
    define bs'' where "bs'' = Stream.shift (stake m bs) bs'"
    have y'': "r bs'' = Some (y, m)"
      by (rule wf_pmfsrD[where bs = bs])
         (use y' assms(1) in \<open>auto simp: bs''_def\<close>)
    have bs'': "sdrop m bs'' = bs'"
      by (auto simp: bs''_def)
    have "Some (x, m+n) \<in> range (bind_pmfsr r f)"
      by (rule range_eqI[of _ _ bs'']) (auto simp: bind_pmfsr_def bs'' y'' x')
    hence "x \<in> fst ` Some -` range (bind_pmfsr r f)"
      by (intro image_eqI[of _ _ "(x, m+n)"]) auto
    thus "x \<in> range_pmfsr (bind_pmfsr r f)"
      using y'' x' bs'' unfolding range_pmfsr_def by blast
  qed
qed

lemma range_map_pmfsr: "range_pmfsr (map_pmfsr f r) = f ` range_pmfsr r"
proof safe
  fix y assume "y \<in> range_pmfsr (map_pmfsr f r)"
  then obtain n bs where bs: "Some (y, n) = map_option (map_prod f id) (r bs)"
    unfolding map_pmfsr_def range_pmfsr_def by auto
  then obtain x where x: "r bs = Some (x, n)" "y = f x"
    by (cases "r bs") auto
  thus "y \<in> f ` range_pmfsr r"
    by (auto simp: x bs intro!: imageI intro: in_range_pmfsrI[of _ bs _ n])
next
  fix x assume "x \<in> range_pmfsr r"
  then obtain bs n where "r bs = Some (x, n)"
    by (auto simp: range_pmfsr_def eq_commute)
  thus "f x \<in> range_pmfsr (map_pmfsr f r)"
    by (intro in_range_pmfsrI[of _ bs _ n]) (auto simp: map_pmfsr_def)
qed
  

lemma wf_bind_pmfsr:
  assumes "wf_pmfsr r"
  assumes "\<And>x. x \<in> range_pmfsr r \<Longrightarrow> wf_pmfsr (f x)"
  shows   "wf_pmfsr (bind_pmfsr r f)"
proof -
  define A where "A = range_pmfsr (bind_pmfsr r f)"
  define B where "B = options (A \<times> (UNIV :: nat set))"
  have "countable A" unfolding A_def using assms
    by (intro countable_subset [OF range_bind_pmfsr_subset] countable_UN countable_range_pmfsr)
       (use assms in \<open>auto simp: wf_pmfsr_def\<close>)
  
  show ?thesis
  proof (rule wf_pmfsrI)
    fix bs bs' :: "bool stream" and x :: 'b and n :: nat
    assume *: "bind_pmfsr r f bs = Some (x, n)" "stake n bs' = stake n bs"
    have r: "wf_pmfsr r"
      using assms(1) by (simp add: wf_pmfsr_def)
    from * obtain y m where ym: "r bs = Some (y, m)" "m \<le> n" "f y (sdrop m bs) = Some (x, n-m)"
      by (auto simp: bind_pmfsr_def Option_bind_conv_case split: option.splits)
    have stake_eq': "stake m bs' = stake m bs"
      using \<open>m \<le> n\<close> * by (metis length_stake stake_sdrop stake_shift_small)
    have ym': "r bs' = Some (y, m)"
      by (rule wf_pmfsrD[OF r, of bs]) (use * ym stake_eq' in auto)

    have "y \<in> range_pmfsr r"
      using ym(1) by (blast intro: in_range_pmfsrI)
    hence fy: "wf_pmfsr (f y)"
      using assms by (auto simp: wf_pmfsr_def)
    have stake_eq'': "stake (n - m) (sdrop m bs') = stake (n - m) (sdrop m bs)"
      by (metis "*"(2) drop_stake)
    have "f y (sdrop m bs') = Some (x, n-m)"
      by (rule wf_pmfsrD[OF fy, of "sdrop m bs"]) (use ym stake_eq'' in auto)
    thus "bind_pmfsr r f bs' = Some (x, n)"
      by (auto simp: ym ym' bind_pmfsr_def)
  qed
qed

lemma wf_map_pmfsr:
  assumes "wf_pmfsr r"
  shows   "wf_pmfsr (map_pmfsr f r)"
  using assms unfolding map_pmfsr_conv_bind_pmfsr
  by (intro wf_bind_pmfsr wf_return_pmfsr)


lemma null_sets_return: "null_sets (return M x) = {X\<in>sets M. x \<notin> X}"
  by (auto simp: null_sets_def)

lemma (in prob_space) distr_stream_space_snth [simp]: 
  assumes "sets M = sets N"
  shows   "distr (stream_space M) N (\<lambda>xs. snth xs n) = M"
proof -
  have "distr (stream_space M) N (\<lambda>xs. snth xs n) = distr (stream_space M) M (\<lambda>xs. snth xs n)"
    by (rule distr_cong) (use assms in auto)
  also have "\<dots> = distr (Pi\<^sub>M UNIV (\<lambda>i. M)) M (\<lambda>f. f n)"
    by (subst stream_space_eq_distr, subst distr_distr) (auto simp: to_stream_def o_def)
  also have "\<dots> = M"
    by (intro distr_PiM_component prob_space_axioms) auto
  finally show ?thesis .
qed

lemma (in prob_space) distr_stream_space_shd [simp]: 
  assumes "sets M = sets N"
  shows   "distr (stream_space M) N shd = M"
  using distr_stream_space_snth[OF assms, of 0] by (simp del: distr_stream_space_snth)

definition loss_pmfsr :: "'a pmfsr \<Rightarrow> real" where
  "loss_pmfsr r = coin_space.prob (r -` {None})"

definition run_pmfsr' :: "'a pmfsr \<Rightarrow> bool stream \<Rightarrow> ('a \<times> bool stream) option" where
  "run_pmfsr' p bs = map_option (\<lambda>(x,n). (x, sdrop n bs)) (p bs)"

definition measure_pmfsr :: "'a pmfsr \<Rightarrow> 'a option measure" where
  "measure_pmfsr p = distr coin_space (count_space UNIV) (map_option fst \<circ> p)"

definition pmfsr_space :: "('a \<times> bool stream) option measure" where
  "pmfsr_space = option_measure (count_space UNIV \<Otimes>\<^sub>M coin_space)"

definition measure_pmfsr' :: "'a pmfsr \<Rightarrow> ('a \<times> bool stream) option measure" where
  "measure_pmfsr' p = distr coin_space pmfsr_space (run_pmfsr' p)"

lemma stream_eqI: "(\<And>n. snth s n = snth s' n) \<Longrightarrow> s = s'"
proof (coinduction arbitrary: s s')
  case (Eq_stream s s')
  have *: "s !! n = s' !! n" for n
    using Eq_stream by auto
  from *[of 0] and *[of "Suc n" for n] show ?case
    by auto
qed

(*
  Central theorem: running the sampler and returning the stream of unused coins is equivalent
  to running the sampler and returning a fresh stream of random coins.

  In other words: if the sampler terminates with result (x, n) then it really did "use" only the
  first n coins and the remaining ones are still "as good as fresh ones".
*)
theorem measure_pmfsr'_conv_measure_pmfsr:
  "measure_pmfsr' p =
     do {
       x \<leftarrow> measure_pmfsr p;
       case x of
         None \<Rightarrow> return pmfsr_space None
       | Some x \<Rightarrow>
           distr coin_space pmfsr_space (\<lambda>bs. Some (x, bs))
     }" (is "_ = bind _ ?f")
proof -
  let ?rhs = "bind (measure_pmfsr p) ?f"
  have 1: "emeasure (measure_pmfsr' p) (Some ` ({x} \<times> Y)) = emeasure ?rhs (Some ` ({x} \<times> Y))"
    if Y: "Y \<in> sets coin_space" for x :: 'a and Y :: "bool stream set"
  proof -
    define X where "X = Some ` ({x} \<times> Y)"
    define B where "B = {stake n bs |bs n. p bs = Some (x, n)}"
  
    have X: "X \<in> sets pmfsr_space"
      sorry
    let ?M = "distr coin_space (count_space UNIV) (map_option fst \<circ> p)"

    have "emeasure (measure_pmfsr' p) X = emeasure coin_space (run_pmfsr' p -` X)"
      unfolding measure_pmfsr'_def using X
      apply (subst emeasure_distr)
        apply (auto simp: space_coin_space)
      sorry
    also have "\<dots> = emeasure coin_space
                      ((\<lambda>bs. map_option (\<lambda>(x, n). (x, sdrop n bs)) (p bs)) -` Some ` ({x} \<times> Y))"
      unfolding run_pmfsr'_def X_def ..
    also have "(\<lambda>bs. map_option (\<lambda>(x, n). (x, sdrop n bs)) (p bs)) -` Some ` ({x} \<times> Y) =
               {bs |bs n. p bs = Some (x, n) \<and> sdrop n bs \<in> Y}"
      by (auto simp: map_option_case inj_image_mem_iff split: option.splits)
    also have "\<dots> = {bs |bs n. p (stake n bs @- sconst False) = Some (x, n) \<and> sdrop n bs \<in> Y}"
      sorry
    also have "\<dots> = (\<Union>n. {bs. p (stake n bs @- sconst False) = Some (x, n) \<and> sdrop n bs \<in> Y})"
      by blast
    also have "emeasure coin_space \<dots> =
                 (\<Sum>i. emeasure coin_space
                    {bs. stake i bs \<in> {bs'. length bs' = i \<and> p (bs' @- sconst False) = Some (x, i)} \<and> sdrop i bs \<in> Y})"
      apply (subst suminf_emeasure [symmetric])
        apply (auto simp: disjoint_family_on_def)
      sorry
    also have "\<dots> = 
       (\<Sum>i. ennreal (real (card {bs'. length bs' = i \<and> p (bs' @- sconst False) = Some (x, i)}) / 2 ^ i) *
             emeasure coin_space Y)"
      apply (subst emeasure_coin_space_stake_sdrop)
       apply auto
      done
    also have "\<dots> = 
       (\<Sum>i. ennreal (real (card {bs'. length bs' = i \<and> p (bs' @- sconst False) = Some (x, i)}) / 2 ^ i)) *
         emeasure coin_space Y"
      by (rule ennreal_suminf_multc)
    also have "(\<Sum>i. ennreal (real (card {bs'. length bs' = i \<and> p (bs' @- sconst False) = Some (x, i)}) / 2 ^ i)) =
               (\<Sum>i. ennreal (real (card {bs'. length bs' = i \<and> p (bs' @- sconst False) = Some (x, i)}) / 2 ^ i) * emeasure coin_space UNIV)"
      by simp      
    also have "\<dots> = (\<Sum>i. emeasure coin_space {bs. p (stake i bs @- sconst False) = Some (x, i)})"
      apply (subst emeasure_coin_space_stake_sdrop [symmetric])
       apply simp
      apply simp
      done
    also have "\<dots> = emeasure coin_space (\<Union>i. {bs. p (stake i bs @- sconst False) = Some (x, i)})"
      apply (subst suminf_emeasure) 
        apply (auto simp: disjoint_family_on_def)
      sorry
    also have "(\<Union>i. {bs. p (stake i bs @- sconst False) = Some (x, i)}) =
               {bs |bs i. p (stake i bs @- sconst False) = Some (x, i)}"
      by auto
    also have "\<dots> = {bs |bs i. p bs = Some (x, i)}"
      sorry
    finally have eq: "emeasure (measure_pmfsr' p) X = emeasure coin_space Y *
                        emeasure coin_space {bs |bs i. p bs = Some (x, i)}"
      by (simp only: mult_ac)

    have "emeasure ?rhs X = (\<integral>\<^sup>+ x. emeasure (?f x) X \<partial>?M)"
      apply (subst emeasure_bind)
         apply (auto simp: measure_pmfsr_def)
      sorry
    also have "\<dots> = \<integral>\<^sup>+ x. emeasure
            (case map_option fst (p x) of None \<Rightarrow> return pmfsr_space None
             | Some x \<Rightarrow> distr coin_space pmfsr_space (\<lambda>bs. Some (x, bs))) X \<partial>coin_space"
      apply (subst nn_integral_distr)
        apply auto
      sorry
    also have "\<dots> = \<integral>\<^sup>+ bs. (case p bs of None \<Rightarrow> indicator X None | 
                            Some (y, _) \<Rightarrow> emeasure coin_space ((\<lambda>bs. Some (y, bs)) -` X))
                           \<partial>coin_space" using X
      apply (intro nn_integral_cong)
      apply (auto split: option.splits)
      apply (subst emeasure_distr)
        apply (auto simp: space_coin_space)
      sorry
    also have "\<dots> = emeasure coin_space Y *
                      \<integral>\<^sup>+ bs. indicator {bs |bs n. p bs = Some (x, n)} bs \<partial>coin_space"
      apply (subst nn_integral_cmult [symmetric])
      defer
    proof (intro nn_integral_cong, goal_cases)
      case (1 bs)
      have "(\<lambda>bs. Some (y, bs)) -` X = (if x = y then Y else {})" for y
        by (auto simp: X_def inj_image_mem_iff)
      hence "(case p bs of None \<Rightarrow> 0 | Some (y, _) \<Rightarrow> emeasure coin_space ((\<lambda>bs. Some (y, bs)) -` X)) =
             emeasure coin_space Y * indicator {bs |bs n. p bs = Some (x, n)} bs"
        by (auto split: option.splits simp: indicator_def)
      thus ?case 
        apply (auto simp: X_def split: option.splits)
        done
    next
      case 2
      show ?case sorry
    qed
    also have "\<dots> = emeasure coin_space Y * emeasure coin_space {bs |bs n. p bs = Some (x, n)}"
      apply (subst nn_integral_indicator)
       apply auto
      sorry
    also have "\<dots> = emeasure (measure_pmfsr' p) X"
      by (rule eq [symmetric])
    finally show ?thesis by (simp only: X_def)
  qed

  have 2: "emeasure (measure_pmfsr' p) X = emeasure ?rhs X"
    if X: "X \<in> sets (option_measure (count_space UNIV \<Otimes>\<^sub>M coin_space))" for X
    sorry

  show ?thesis
    apply (rule measure_eqI)
    subgoal
     apply (simp add: measure_pmfsr'_def pmfsr_space_def)
     apply (subst sets_bind[of _ _ pmfsr_space])
        apply (auto split: option.splits simp: pmfsr_space_def measure_pmfsr_def)
      done
    apply (rule 2)
    apply (auto simp: measure_pmfsr'_def pmfsr_space_def)
    done
qed

lemma measure_pmfsr_conv_measure_pmfsr':
  "measure_pmfsr r = distr (measure_pmfsr' r) (count_space UNIV) (map_option fst)"
  unfolding measure_pmfsr_def measure_pmfsr'_def
  apply (subst distr_distr)
    defer
    defer
  apply (rule arg_cong[of _ _ "distr coin_space (count_space UNIV)"])
    apply (auto simp: run_pmfsr'_def fun_eq_iff map_option_case split: option.splits)
  sorry


lemma measure_bind_pmfsr:
  assumes "wf_pmfsr r"
  assumes "\<And>x. x \<in> range_pmfsr r \<Longrightarrow> wf_pmfsr (f x)"
  shows   "measure_pmfsr (bind_pmfsr r f) =
             do {x \<leftarrow> measure_pmfsr r;
                 case x of
                   None \<Rightarrow> return (count_space UNIV) None
                 | Some x \<Rightarrow> measure_pmfsr (f x)}"
proof -
  have "measure_pmfsr (bind_pmfsr r f) = 
        distr coin_space (count_space UNIV)
          (\<lambda>bs. case r bs of None \<Rightarrow> None | Some (y, n) \<Rightarrow> map_option fst (f y (sdrop n bs)))"
    unfolding measure_pmfsr_def bind_pmfsr_def
    by (intro arg_cong[of _ _ "distr coin_space (count_space UNIV)"])
       (auto split: option.splits simp: fun_eq_iff Option_bind_conv_case)

  have "do {x \<leftarrow> measure_pmfsr r;
            case x of
              None \<Rightarrow> return (count_space UNIV) None
            | Some x \<Rightarrow> measure_pmfsr (f x)} =
        distr (
           do {x \<leftarrow> measure_pmfsr r;
             case x of
               None \<Rightarrow> return pmfsr_space None
             | Some x \<Rightarrow> distr coin_space pmfsr_space (\<lambda>bs. Some (x, bs))})
       (count_space UNIV)
       (\<lambda>x. case x of None \<Rightarrow> None | Some (x, bs') \<Rightarrow> map_option fst (f x bs'))"
    apply (subst distr_bind[where K = pmfsr_space])
    prefer 4
       apply (intro bind_cong refl)
       apply (auto split: option.splits simp: measure_pmfsr_def o_def)
        apply (subst distr_return)
          apply (auto)
         prefer 3
         apply (subst distr_distr)
           apply (auto)
           prefer 3
           apply (rule arg_cong[of _ _ "distr coin_space (count_space UNIV)"])
           apply (auto simp: fun_eq_iff split: option.splits)
    sorry
  also have "do {x \<leftarrow> measure_pmfsr r;
             case x of
               None \<Rightarrow> return pmfsr_space None
             | Some x \<Rightarrow> distr coin_space pmfsr_space (\<lambda>bs. Some (x, bs))} =
             measure_pmfsr' r"
    by (rule measure_pmfsr'_conv_measure_pmfsr [symmetric])
  also have "distr (measure_pmfsr' r) (count_space UNIV) 
               (\<lambda>x. case x of None \<Rightarrow> None | Some (x, bs') \<Rightarrow> map_option fst (f x bs')) =
             distr coin_space (count_space UNIV)
               (\<lambda>bs. case r bs of None \<Rightarrow> None | Some (y, n) \<Rightarrow> map_option fst (f y (sdrop n bs)))"
    unfolding measure_pmfsr'_def
    apply (subst distr_distr)
    prefer 3
    apply (rule arg_cong[of _ _ "distr coin_space (count_space UNIV)"])
      apply (auto simp: o_def fun_eq_iff run_pmfsr'_def split: option.splits)
    sorry
  also have "\<dots> = measure_pmfsr (bind_pmfsr r f)"
    unfolding measure_pmfsr_def bind_pmfsr_def
    by (intro arg_cong[of _ _ "distr coin_space (count_space UNIV)"])
       (auto split: option.splits simp: fun_eq_iff Option_bind_conv_case)
  finally show ?thesis ..
qed

context
begin

interpretation pmf_as_measure .

lift_definition spmf_of_pmfsr :: "'a pmfsr \<Rightarrow> 'a spmf" is
  "\<lambda>r. if wf_pmfsr r then measure_pmfsr r
       else return (count_space UNIV) None"
proof goal_cases
  case (1 r)
  define M where "M = (if wf_pmfsr r then
                         measure_pmfsr r
                       else return (count_space UNIV) None)"
  have "coin_space.random_variable (count_space UNIV) (map_option fst \<circ> r)" if "wf_pmfsr r"
    by (rule measurable_comp[OF measurable_pmfsr[OF that]]) auto
  then interpret M: prob_space M
    by (auto simp: M_def measure_pmfsr_def intro!: coin_space.prob_space_distr prob_space_return)
  show ?case
    unfolding M_def [symmetric]
  proof (intro conjI)
    show "prob_space M"
      by (fact M.prob_space_axioms)
  next
    show "sets M = UNIV"
      by (simp add: M_def measure_pmfsr_def)
  next
    show "AE x in M. Sigma_Algebra.measure M {x} \<noteq> 0"
    proof (cases "wf_pmfsr r")
      case True
      have meas: "coin_space.random_variable (count_space UNIV) (map_option fst \<circ> r)"
        by (rule measurable_comp[OF measurable_pmfsr[OF True]]) auto
      show ?thesis
      proof (subst M.AE_support_countable)
        have "AE x in coin_space. map_option fst (r x) \<in> options (range_pmfsr r)"
          by (intro always_eventually)
             (auto simp: options_def map_option_case intro: imageI in_range_pmfsrI split: option.splits)
        hence "AE x in M. x \<in> options (range_pmfsr r)"
          unfolding M_def measure_pmfsr_def using True meas by (simp add: AE_distr_iff)
        thus "\<exists>S. countable S \<and> (AE x in M. x \<in> S)"
          by (intro exI[of _ "options (range_pmfsr r)"]) (use True countable_range_pmfsr in auto)
      qed (auto simp: M_def measure_pmfsr_def)
    next
      case False
      thus ?thesis
        unfolding M_def by (auto simp: AE_return measure_return)
    qed
  qed
qed

end

lemma loss_pmfsr_altdef:
  assumes "wf_pmfsr r"
  shows   "loss_pmfsr r = pmf (spmf_of_pmfsr r) None"
proof -
  have "(map_option fst \<circ> r) -` {None} = r -` {None}"
    by auto
  moreover have "coin_space.random_variable (count_space UNIV) (map_option fst \<circ> r)"
    by (intro measurable_comp[OF measurable_pmfsr] assms) auto
  ultimately show ?thesis
    using assms
    by (auto simp: loss_pmfsr_def pmf.rep_eq spmf_of_pmfsr.rep_eq measure_pmfsr_def 
                   measure_distr space_coin_space)
qed

lemma weight_pmfsr: "wf_pmfsr r \<Longrightarrow> weight_spmf (spmf_of_pmfsr r) = 1 - loss_pmfsr r"
  by (simp add: weight_spmf_conv_pmf_None loss_pmfsr_altdef)

lemma spmf_of_return_pmfsr [simp]:
  "spmf_of_pmfsr (return_pmfsr x) = return_spmf x"
proof -
  have "measure_pmf (spmf_of_pmfsr (return_pmfsr x)) =
          distr coin_space (count_space UNIV) (map_option fst \<circ> return_pmfsr x)"
    by (subst spmf_of_pmfsr.rep_eq) (auto simp: wf_return_pmfsr measure_pmfsr_def)
  also have "map_option fst \<circ> return_pmfsr x = (\<lambda>_. Some x)"
    by (auto simp: fun_eq_iff return_pmfsr_def)
  also have "distr coin_space (count_space UNIV) \<dots> = return (count_space UNIV) (Some x)"
    by simp
  also have "\<dots> = measure_pmf (return_spmf x)"
    by (simp add: return_pmf.rep_eq)
  finally show ?thesis
    using measure_pmf_inject by auto
qed

lemma loss_return_pmfsr [simp]: "loss_pmfsr (return_pmfsr x) = 0"
  by (simp add: loss_pmfsr_altdef wf_return_pmfsr)

lemma spmf_of_coin_pmfsr [simp]:
  "spmf_of_pmfsr coin_pmfsr = coin_spmf"
proof -
  have "measure_pmf (spmf_of_pmfsr coin_pmfsr) =
          distr coin_space (count_space UNIV) (map_option fst \<circ> coin_pmfsr)"
    by (subst spmf_of_pmfsr.rep_eq) (auto simp: wf_coin_pmfsr measure_pmfsr_def)
  also have "map_option fst \<circ> coin_pmfsr = Some \<circ> shd"
    by (auto simp: fun_eq_iff coin_pmfsr_def)
  also have "distr coin_space (count_space UNIV) \<dots> =
               distr (distr coin_space (count_space UNIV) shd) (count_space UNIV) Some"
    by (subst distr_distr) (auto simp: coin_space_def)
  also have "distr coin_space (count_space UNIV) shd = measure_pmf (pmf_of_set UNIV)"
    unfolding coin_space_def by simp
  also have "distr (measure_pmf (pmf_of_set UNIV)) (count_space UNIV) Some =
             measure_pmf (map_pmf Some (pmf_of_set UNIV))"
    by (rule map_pmf_rep_eq [symmetric])
  also have "\<dots> = measure_pmf coin_spmf"
    unfolding spmf_of_set_def spmf_of_pmf_def by simp
  finally show ?thesis
    using measure_pmf_inject by auto
qed

lemma loss_coin_pmfsr [simp]: "loss_pmfsr coin_pmfsr = 0"
  by (simp add: loss_pmfsr_altdef wf_coin_pmfsr)

lemma spmf_of_bind_pmfsr:
  assumes "wf_pmfsr r"
  assumes "\<And>x. x \<in> range_pmfsr r \<Longrightarrow> wf_pmfsr (f x)"
  shows   "spmf_of_pmfsr (bind_pmfsr r f) = bind_spmf (spmf_of_pmfsr r) (spmf_of_pmfsr \<circ> f)"
proof -
  note meas1 [measurable] = measurable_pmfsr [OF assms(1)]
  note meas2 [measurable] = measurable_pmfsr [OF assms(2)]
  have r: "measure_pmfsr r = measure_pmf (spmf_of_pmfsr r)"
    using assms(1) by (simp add: spmf_of_pmfsr.rep_eq)

  have "measure_pmf (spmf_of_pmfsr (bind_pmfsr r f)) = measure_pmfsr (bind_pmfsr r f)"
    using assms wf_bind_pmfsr by (subst spmf_of_pmfsr.rep_eq) auto
  also have "\<dots> = measure_pmfsr r \<bind>
                  case_option (return (count_space UNIV) None) (\<lambda>x. measure_pmfsr (f x))"
    using assms by (subst measure_bind_pmfsr) auto
  also have "\<dots> = measure_pmf (bind_spmf (spmf_of_pmfsr r) (spmf_of_pmfsr \<circ> f))"
    unfolding bind_spmf_def bind_pmf.rep_eq o_def id_def r
    apply (intro bind_cong_AE)
       apply (auto simp: AE_measure_pmf_iff)
      prefer 3
    using assms(2)
      apply (auto split: option.splits simp: return_pmf.rep_eq spmf_of_pmfsr.rep_eq)
    sorry
  finally show ?thesis
    using measure_pmf_inject by auto
qed

lemma prob_measure_pmfsr:
   "wf_pmfsr r \<Longrightarrow>
      Sigma_Algebra.measure (measure_pmfsr r) X =
        coin_space.prob ((map_option fst \<circ> r) -` X)"
  unfolding measure_pmfsr_def
  by (subst measure_distr) (auto intro!: measurable_comp measurable_pmfsr simp: space_coin_space)

lemma emeasure_measure_pmfsr:
   "wf_pmfsr r \<Longrightarrow> emeasure (measure_pmfsr r) X = emeasure coin_space ((map_option fst \<circ> r) -` X)"
  by (metis coin_space.emeasure_eq_measure measure_pmf.emeasure_eq_measure prob_measure_pmfsr spmf_of_pmfsr.rep_eq)

lemma prob_space_measure_pmfsr: "wf_pmfsr r \<Longrightarrow> prob_space (measure_pmfsr r)"
  unfolding measure_pmfsr_def
  by (intro coin_space.prob_space_distr measurable_comp[OF measurable_pmfsr]) auto

lemma prob_coin_space_stake_eq:
  assumes "length xs = n"
  shows   "coin_space.prob {bs. stake n bs = xs} = 1 / 2 ^ n"
proof -
  have "emeasure coin_space {bs. stake n bs \<in> {xs} \<and> sdrop n bs \<in> UNIV} =
        ennreal (real (card {xs}) / 2 ^ n) * emeasure coin_space UNIV"
    by (rule emeasure_coin_space_stake_sdrop) (use assms in auto)
  hence "emeasure coin_space {bs. stake n bs = xs} = ennreal (1 / 2 ^ n)"
    by simp
  thus ?thesis
    by (simp add: coin_space.emeasure_eq_measure)
qed    

lemma set_spmf_of_pmfsr:
  assumes  "wf_pmfsr r"
  shows    "set_spmf (spmf_of_pmfsr r) = range_pmfsr r"
proof (intro equalityI subsetI)
  fix x :: 'a
  have "x \<notin> set_spmf (spmf_of_pmfsr r)" if "x \<notin> range_pmfsr r"
  proof -
    have "spmf (spmf_of_pmfsr r) x = Sigma_Algebra.measure (measure_pmfsr r) {Some x}"
      unfolding pmf.rep_eq spmf_of_pmfsr.rep_eq using assms by auto
    also have "\<dots> = coin_space.prob ((map_option fst \<circ> r) -` {Some x})"
      unfolding measure_pmfsr_def
      by (subst measure_distr)
         (auto intro: measurable_comp[OF measurable_pmfsr[OF assms]] simp: space_coin_space)
    also have "(map_option fst \<circ> r) -` {Some x} = {}"
      using \<open>x \<notin> range_pmfsr r\<close> in_range_pmfsrI[of r _ x] by fastforce
    finally have "spmf (spmf_of_pmfsr r) x = 0"
      by simp
    thus "x \<notin> set_spmf (spmf_of_pmfsr r)"
      by (simp add: spmf_eq_0_set_spmf)
  qed
  thus "x \<in> range_pmfsr r" if "x \<in> set_spmf (spmf_of_pmfsr r)"
    using that by blast
next
  fix x :: 'a
  assume "x \<in> range_pmfsr r"
  then obtain bs n where x: "r bs = Some (x, n)"
    by (elim in_range_pmfsrE)
  define bs' where "bs' = stake n bs"
  have "0 < coin_space.prob {bs. stake n bs = bs'}"
    by (subst prob_coin_space_stake_eq) (auto simp: bs'_def)
  also have "{bs. stake n bs = bs'} = (stake n -` {bs'} \<inter> space coin_space)"
    by (auto simp: space_coin_space)
  also have "coin_space.prob \<dots> \<le>
             coin_space.prob ((map_option fst \<circ> r) -` {Some x} \<inter> space coin_space)"
  proof (intro coin_space.finite_measure_mono Int_mono order.refl)
    show "stake n -` {bs'} \<subseteq> (map_option fst \<circ> r) -` {Some x}"
      using wf_pmfsrD[OF assms, of bs x n] x
      by (auto simp: coin_space_def space_stream_space bs'_def)
    show "(map_option fst \<circ> r) -` {Some x} \<inter> space coin_space \<in> coin_space.events"
      by (rule measurable_sets[of _ _ "count_space UNIV"] measurable_comp measurable_pmfsr assms)+
         auto
  qed
  also have "\<dots> = Sigma_Algebra.measure (measure_pmfsr r) {Some x}"
    using assms by (subst prob_measure_pmfsr) (auto simp: space_coin_space)
  also have "\<dots> = spmf (spmf_of_pmfsr r) x"
    using assms by (auto simp: spmf_of_pmfsr.rep_eq pmf.rep_eq)
  finally show "x \<in> set_spmf (spmf_of_pmfsr r)"
    using spmf_eq_0_set_spmf[of "spmf_of_pmfsr r" x] by simp
qed


lemma loss_bind_pmfsr:
  assumes "wf_pmfsr r"
  assumes "\<And>x. x \<in> range_pmfsr r \<Longrightarrow> wf_pmfsr (f x)" 
  shows   "loss_pmfsr (bind_pmfsr r f) = loss_pmfsr r +
             (LINT x|measure_spmf (spmf_of_pmfsr r). loss_pmfsr (f x))"
proof -
  have "loss_pmfsr (bind_pmfsr r f) = pmf (spmf_of_pmfsr (r \<bind> f)) None"
    by (subst loss_pmfsr_altdef) (auto intro!: wf_bind_pmfsr assms)
  also have "spmf_of_pmfsr (r \<bind> f) = spmf_of_pmfsr r \<bind> (spmf_of_pmfsr \<circ> f)"
    by (rule spmf_of_bind_pmfsr) (auto intro!: assms)
  also have "pmf \<dots> None = loss_pmfsr r +
               (LINT x|measure_spmf (spmf_of_pmfsr r). pmf (spmf_of_pmfsr (f x)) None)"
    by (subst pmf_bind_spmf_None) (auto simp: assms loss_pmfsr_altdef o_def)
  also have "(LINT x|measure_spmf (spmf_of_pmfsr r). pmf (spmf_of_pmfsr (f x)) None) =
             (LINT x|measure_spmf (spmf_of_pmfsr r). loss_pmfsr (f x))"
  proof (intro Bochner_Integration.integral_cong_AE)
    have "AE x in measure_spmf (spmf_of_pmfsr r). x \<in> set_spmf (spmf_of_pmfsr r)"
      using AE_measure_spmf_iff by blast
    hence "AE x in measure_spmf (spmf_of_pmfsr r). x \<in> range_pmfsr r"
      by eventually_elim (use assms(1) set_spmf_of_pmfsr in blast)
    thus "AE x in measure_spmf (spmf_of_pmfsr r).
            pmf (spmf_of_pmfsr (f x)) None = loss_pmfsr (f x)"
      by eventually_elim (auto simp: loss_pmfsr_altdef assms)
  qed auto
  finally show ?thesis .
qed

lemma spmf_of_map_pmfsr:
  assumes "wf_pmfsr r"
  shows   "spmf_of_pmfsr (map_pmfsr f r) = map_spmf f (spmf_of_pmfsr r)"
  using assms
  by (simp add: map_pmfsr_conv_bind_pmfsr spmf_of_bind_pmfsr wf_return_pmfsr 
                o_def map_spmf_conv_bind_spmf)

lemma loss_map_pmfsr [simp]: "loss_pmfsr (map_pmfsr f r) = loss_pmfsr r"
proof -
  have "map_pmfsr f r -` {None} = r -` {None}"
    by (auto simp: map_pmfsr_def)
  thus ?thesis
    by (simp add: loss_pmfsr_def)
qed



definition ord_pmfsr :: "'a pmfsr \<Rightarrow> 'a pmfsr \<Rightarrow> bool" where
  "ord_pmfsr = rel_fun (=) (ord_option (=))"

lemma ord_pmfsrD: "ord_pmfsr r s \<Longrightarrow> r bs = Some xn \<Longrightarrow> s bs = Some xn"
  unfolding ord_pmfsr_def rel_fun_def
  by (metis ord_option_eq_simps(2))

context fixes Y :: "'a pmfsr set" begin

definition lub_pmfsr :: "'a pmfsr" where
  "lub_pmfsr bs = 
     (let X = {xn |xn r. r \<in> Y \<and> r bs = Some xn}
      in  if Set.is_singleton X then Some (the_elem X) else None)"

lemma lub_pmfsr_eq_SomeI:
  assumes "r \<in> Y" "r bs = Some xn"
  assumes "\<And>r' xn'. r' \<in> Y \<Longrightarrow> r' bs = Some xn' \<Longrightarrow> xn' = xn"
  shows   "lub_pmfsr bs = Some xn"
proof -
  have *: "{xn |xn r. r \<in> Y \<and> r bs = Some xn} = {xn}"
    using assms by blast
  show ?thesis
    unfolding Let_def lub_pmfsr_def * by auto
qed

lemma lub_pmfsr_eq_SomeI':
  assumes "r \<in> Y" "r bs = Some xn" "Complete_Partial_Order.chain ord_pmfsr Y"
  shows   "lub_pmfsr bs = Some xn"
proof (rule lub_pmfsr_eq_SomeI[OF assms(1,2)])
  fix r' xn' assume r': "r' \<in> Y" "r' bs = Some xn'"
  with assms have "ord_pmfsr r r' \<or> ord_pmfsr r' r"
    by (auto simp: Complete_Partial_Order.chain_def)
  thus "xn' = xn"
    using ord_pmfsrD r' assms by (metis option.inject ord_pmfsrD)
qed

lemma lub_pmfsr_eq_SomeE:
  assumes "lub_pmfsr bs = Some xn"
  obtains r where "r \<in> Y" "r bs = Some xn"
  using assms
  by (auto simp: lub_pmfsr_def Let_def is_singleton_def split: if_splits)

lemma lub_pmfsr_eq_SomeD:
  assumes "lub_pmfsr bs = Some xn" "r \<in> Y" "r bs = Some xn'"
  shows   "xn' = xn"
proof -
  let ?X = "{xn |xn r. r \<in> Y \<and> r bs = Some xn}"
  from assms(1) have "is_singleton ?X"
    by (auto simp: lub_pmfsr_def Let_def split: if_splits)
  then obtain xn'' where xn'': "?X = {xn''}"
    by (auto simp: is_singleton_def)
  moreover have "xn' \<in> ?X"
    using assms by auto
  ultimately show "xn' = xn"
    using assms unfolding lub_pmfsr_def Let_def xn'' by auto
qed

end

lemma wf_lub_pmfsr:
  assumes "Complete_Partial_Order.chain ord_pmfsr Y" "\<And>r. r \<in> Y \<Longrightarrow> wf_pmfsr r"
  shows   "wf_pmfsr (lub_pmfsr Y)"
proof (rule wf_pmfsrI)
  fix bs bs' x n
  assume *: "lub_pmfsr Y bs = Some (x, n)" "stake n bs' = stake n bs"
  from *(1) obtain r where r: "r \<in> Y" "r bs = Some (x, n)"
    by (auto elim!: lub_pmfsr_eq_SomeE)
  show "lub_pmfsr Y bs' = Some (x, n)"
  proof (rule lub_pmfsr_eq_SomeI)
    show "r \<in> Y"
      by fact
    show "r bs' = Some (x, n)"
      by (rule wf_pmfsrD[where bs = bs]) (use assms r * in auto)
    fix r' xn'
    assume r': "r' \<in> Y" "r' bs' = Some xn'"
    have "ord_pmfsr r' r \<or> ord_pmfsr r r'"
      using assms r r' by (auto simp: Complete_Partial_Order.chain_def)
    hence "ord_option (=) (r' bs') (r bs') \<or> ord_option (=) (r bs') (r' bs')"
      by (auto simp: ord_pmfsr_def rel_fun_def)
    thus "xn' = (x, n)"
      using \<open>r bs' = Some (x, n)\<close> r' by (cases "r' bs'") auto
  qed
qed    


lemma lub_pmfsr_empty [simp]: "lub_pmfsr {} = (\<lambda>_. None)"
  by (auto simp: lub_pmfsr_def fun_eq_iff is_singleton_def)

lemma lub_pmfsr_const [simp]: "lub_pmfsr {p} = p"
proof
  fix bs :: "bool stream"
  show "lub_pmfsr {p} bs = p bs"
  proof (cases "p bs")
    case None
    hence *: "{xn |xn r. r \<in> {p} \<and> r bs = Some xn} = {}"
      by auto
    show ?thesis
      unfolding lub_pmfsr_def Let_def * by (auto simp: is_singleton_def None)
  next
    case (Some xn)
    hence *: "{xn |xn r. r \<in> {p} \<and> r bs = Some xn} = {xn}"
      by auto
    show ?thesis
      unfolding lub_pmfsr_def Let_def * by (auto simp: is_singleton_def Some)
  qed
qed

lemma partial_function_definitions_pmfsr: 
  "partial_function_definitions ord_pmfsr lub_pmfsr"
  (is "partial_function_definitions ?R _")
proof
  fix x show "?R x x"
    by (auto simp: ord_pmfsr_def rel_fun_def intro: ord_option_reflI)
next
  fix x y z
  assume "?R x y" "?R y z"
  with transp_ord_option[OF transp_equality] show "?R x z"
    unfolding ord_pmfsr_def by (fastforce simp: rel_fun_def transp_def)    
next
  fix x y
  assume "?R x y" "?R y x"
  thus "x = y"
    using antisymp_ord_option[of "(=)"]
    by (fastforce simp: ord_pmfsr_def rel_fun_def antisymp_def)
next
  fix Y r
  assume Y: "Complete_Partial_Order.chain ?R Y" "r \<in> Y"
  show "?R r (lub_pmfsr Y)"
    unfolding ord_pmfsr_def rel_fun_def
  proof safe
    fix bs :: "bool stream"
    show "ord_option (=) (r bs) (lub_pmfsr Y bs)"
    proof (cases "r bs")
      case None
      thus ?thesis
        by auto
    next
      case [simp]: (Some xn)
      have "{xn |xn r. r \<in> Y \<and> r bs = Some xn} = {xn}"
      proof (intro equalityI subsetI)
        fix xn' assume "xn' \<in> {xn |xn r. r \<in> Y \<and> r bs = Some xn}"
        then obtain r' where *: "r' \<in> Y" "r' bs = Some xn'"
          by auto
        from Y * have "ord_pmfsr r r' \<or> ord_pmfsr r' r"
          unfolding Complete_Partial_Order.chain_def by blast
        hence "ord_option (=) (r bs) (r' bs) \<or> ord_option (=) (r' bs) (r bs)"
          unfolding ord_pmfsr_def rel_fun_def by blast
        with * have "xn = xn'"
          by auto
        thus "xn' \<in> {xn}"
          by simp
      qed (use Y(2) in auto)
      hence "lub_pmfsr Y bs = Some xn"
        by (simp add: lub_pmfsr_def)
      thus ?thesis
        by simp
    qed
  qed
next
  fix Y r
  assume Y: "Complete_Partial_Order.chain ?R Y" and upper: "\<And>r'. r' \<in> Y \<Longrightarrow> ?R r' r"
  show "?R (lub_pmfsr Y) r"
    unfolding ord_pmfsr_def rel_fun_def
  proof safe
    fix bs :: "bool stream"
    show "ord_option (=) (lub_pmfsr Y bs) (r bs)"
    proof (cases "lub_pmfsr Y bs")
      case None
      thus ?thesis
        by auto
    next
      case (Some xn)
      then obtain r' where r': "r' \<in> Y" "r' bs = Some xn"
        by (elim lub_pmfsr_eq_SomeE)
      have "?R r' r"
        by (rule upper) fact+
      hence "ord_option (=) (r' bs) (r bs)"
        by (auto simp: ord_pmfsr_def rel_fun_def)
      with r' Some show ?thesis
        by auto
    qed
  qed
qed

lemma ccpo_pmfsr: "class.ccpo lub_pmfsr ord_pmfsr (mk_less ord_pmfsr)"
  by (rule ccpo partial_function_definitions_pmfsr)+

interpretation pmfsr: partial_function_definitions "ord_pmfsr" "lub_pmfsr"
  rewrites "lub_pmfsr {} \<equiv> (\<lambda>_. None)"
  by (rule partial_function_definitions_pmfsr) simp


lemma mono_spmf_of_pmfsr:
  assumes "wf_pmfsr r" "wf_pmfsr s" "ord_pmfsr r s"
  shows   "ord_spmf (=) (spmf_of_pmfsr r) (spmf_of_pmfsr s)"
proof (rule ord_pmf_increaseI)
  fix x :: 'a
  have "coin_space.prob ((map_option fst \<circ> r) -` {Some x}) \<le>
        coin_space.prob ((map_option fst \<circ> s) -` {Some x})"
  proof (rule coin_space.finite_measure_mono)
    have "s bs = Some (x, n)" if "r bs = Some (x, n)" for bs n
      using ord_pmfsrD[OF assms(3)] that by blast
    thus "(map_option fst \<circ> r) -` {Some x} \<subseteq> (map_option fst \<circ> s) -` {Some x}"
      unfolding o_def by auto
  next
    show "(map_option fst \<circ> s) -` {Some x} \<in> coin_space.events"
      by (rule measurable_sets_space_UNIV[of _ _ "count_space UNIV"]
               measurable_comp measurable_pmfsr[OF assms(2)])+ (auto simp: space_coin_space)
  qed
  thus "spmf (spmf_of_pmfsr r) x \<le> spmf (spmf_of_pmfsr s) x"
    using assms by (auto simp: pmf.rep_eq spmf_of_pmfsr.rep_eq prob_measure_pmfsr)
qed auto

definition prefixes_pmfsr :: "'a pmfsr \<Rightarrow> bool list set"
  where "prefixes_pmfsr r = {stake n bs |bs x n. r bs = Some (x, n)}"

definition prefix_pmfsr :: "'a pmfsr \<Rightarrow> bool list \<Rightarrow> 'a" where
  "prefix_pmfsr r bs = fst (the (r (bs @- sconst False)))"

lemma prefix_pmfsr:
  assumes "bs \<in> prefixes_pmfsr r" "wf_pmfsr r" "stake (length bs) bs' = bs"
  shows   "r bs' = Some (prefix_pmfsr r bs, length bs)"
proof -
  from assms(1) obtain x bs'' where 1: "r bs'' = Some (x, length bs)" "stake (length bs) bs'' = bs"
    by (auto simp: prefixes_pmfsr_def)
  have "r (bs @- sconst False) = Some (x, length bs)"
    by (rule wf_pmfsrD[OF assms(2) 1(1)]) (use 1(2) in auto)
  hence 2: "\<exists>x. r (bs @- sconst False) = Some (x, length bs)"
    by auto
  have 3: "r bs' = Some (x, length bs)" if "r (bs @- sconst False) = Some (x, length bs)" for x
    by (rule wf_pmfsrD[OF assms(2) that]) (use assms in auto)
  show ?thesis unfolding prefix_pmfsr_def
    using 1 2 3 by auto
qed

lemma take_prefix: "prefix xs ys \<Longrightarrow> take (length xs) ys = xs"
  unfolding prefix_def by auto

lemma prefixes_pmfsr_orthogonal:
  assumes "wf_pmfsr r" "bs1 \<in> prefixes_pmfsr r" "bs2 \<in> prefixes_pmfsr r" "prefix bs1 bs2"
  shows   "bs1 = bs2"
proof -
  have len: "length bs1 \<le> length bs2"
    using assms(4) by (simp add: prefix_length_le)
  have "r (bs2 @- sconst False) = Some (prefix_pmfsr r bs1, length bs1)"
    using assms len by (intro prefix_pmfsr) (auto simp: take_prefix)
  also have "r (bs2 @- sconst False) = Some (prefix_pmfsr r bs2, length bs2)"
    using assms len by (intro prefix_pmfsr) auto
  finally have "length bs1 = length bs2"
    by simp
  with \<open>prefix bs1 bs2\<close> show ?thesis
    using take_prefix[of bs1 bs2] by simp
qed

lemma emeasure_measure_pmfsr:
  assumes "wf_pmfsr r"
  shows   "emeasure (measure_pmfsr r) (Some ` X) =
             (\<Sum>n. ennreal (card {bs. stake n bs \<in> (prefix_pmfsr r -` X \<inter> prefixes_pmfsr r)} / 2 ^ n))"
  oops

lemma prefixes_pmfsr_mono:
  assumes "ord_pmfsr r s"
  shows   "prefixes_pmfsr r \<subseteq> prefixes_pmfsr s"
  using assms ord_pmfsrD[of r s] unfolding prefixes_pmfsr_def by blast

lemma ord_option_altdef:
  "ord_option le x y \<longleftrightarrow>
     (case x of None \<Rightarrow> True | Some x' \<Rightarrow> (case y of None \<Rightarrow> False | Some y' \<Rightarrow> le x' y'))"
  by (auto split: option.splits)

lemma chain_imp_ord_pmfsr_iff_prefixes_subset:
  assumes "Complete_Partial_Order.chain ord_pmfsr Y" "r \<in> Y" "s \<in> Y" "wf_pmfsr r" "wf_pmfsr s"
  shows   "ord_pmfsr r s \<longleftrightarrow> prefixes_pmfsr r \<subseteq> prefixes_pmfsr s"
proof
  assume *: "prefixes_pmfsr r \<subseteq> prefixes_pmfsr s"
  show "ord_pmfsr r s"
  proof (cases "ord_pmfsr r s")
    case False
    with assms have 1: "ord_pmfsr s r"
      by (auto simp: Complete_Partial_Order.chain_def)
    from False obtain bs x n where 2: "r bs = Some (x, n)" "\<forall>m. s bs = Some (x, m) \<longrightarrow> m \<noteq> n"
      by (auto simp: ord_pmfsr_def rel_fun_def ord_option_altdef split: option.splits)
    with ord_pmfsrD[OF 1, of bs] have 3: "s bs = None"
      by (cases "s bs") auto
    have "stake n bs \<in> prefixes_pmfsr r"
      using 2 by (auto simp: prefixes_pmfsr_def)
    also note *
    finally have "stake n bs \<in> prefixes_pmfsr s" .
    with 3 have False
      using \<open>wf_pmfsr s\<close> by (simp add: prefix_pmfsr)
    thus ?thesis ..
  qed
qed (rule prefixes_pmfsr_mono)

lemma space_measure_pmfsr: "space (measure_pmfsr r) = UNIV"
  by (simp add: measure_pmfsr_def)

lemma sets_measure_pmfsr: "sets (measure_pmfsr r) = UNIV"
  by (simp add: measure_pmfsr_def)

definition measure_pmfsr'' :: "'a pmfsr \<Rightarrow> 'a measure" where
  "measure_pmfsr'' r = distr (restrict_space (measure_pmfsr r) (range Some)) (count_space UNIV) the"

lemma measurable_the_measure_pmfsr_Some [measurable, simp]:
  "the \<in> measurable (restrict_space (measure_pmfsr p) (range Some)) (count_space UNIV)"
  by (auto simp add: measurable_def sets_restrict_space space_restrict_space
                     integral_restrict_space measure_pmfsr_def)

lemma subprob_space_measure_pmfsr'':
  assumes "wf_pmfsr r"
  shows   "subprob_space (measure_pmfsr'' r)"
proof -
  interpret prob_space "measure_pmfsr r"
    by (rule prob_space_measure_pmfsr) fact
  interpret A: subprob_space "restrict_space (measure_pmfsr r) (range Some)"
    by (rule subprob_space_restrict_space[OF subprob_space_axioms]) (auto simp: measure_pmfsr_def)
  show ?thesis
    unfolding measure_pmfsr''_def by (intro A.subprob_space_distr) auto
qed

lemma emeasure_measure_pmfsr'':
  assumes "wf_pmfsr r"
  shows   "emeasure (measure_pmfsr'' r) X = emeasure (measure_pmfsr r) (Some ` X)"
proof -
  have "emeasure (measure_pmfsr'' r) X = 
          emeasure (restrict_space (measure_pmfsr r) (range Some)) (the -` X \<inter> range Some)"
    unfolding measure_pmfsr''_def
    by (subst emeasure_distr) (auto simp: space_restrict_space space_measure_pmfsr)
  also have "emeasure (restrict_space (measure_pmfsr r) (range Some)) (the -` X \<inter> range Some) =
             emeasure (measure_pmfsr r) (the -` X \<inter> range Some)"
    by (subst emeasure_restrict_space) (auto simp: space_measure_pmfsr sets_measure_pmfsr)
  also have "the -` X \<inter> range Some = Some ` X"
    by auto
  finally show ?thesis .
qed

lemma prob_measure_pmfsr'':
  assumes "wf_pmfsr r"
  shows   "Sigma_Algebra.measure (measure_pmfsr'' r) X =
           Sigma_Algebra.measure (measure_pmfsr r) (Some ` X)"
  using assms by (simp add: Sigma_Algebra.measure_def emeasure_measure_pmfsr'')

lemma restrict_distr':
  assumes [measurable]: "f \<in> measurable M N"
  assumes [simp]: "\<Omega> \<inter> space N \<in> sets N" and restrict: "f \<in> space M \<rightarrow> \<Omega>"
  shows "restrict_space (distr M N f) \<Omega> =
         distr (restrict_space M (f -` \<Omega> \<inter> space M)) (restrict_space N \<Omega>) f"
proof (rule measure_eqI)
  fix X assume X: "X \<in> sets (restrict_space (distr M N f) \<Omega>)"
  have X': "X \<in> sets N"
    using X apply (simp add: sets_restrict_space)
    by (metis assms(2) sets_restrict_space sets_restrict_space_iff)
  have "emeasure (distr (restrict_space M (f -` \<Omega> \<inter> space M)) (restrict_space N \<Omega>) f) X =
          emeasure (restrict_space M (f -` \<Omega> \<inter> space M)) 
          (f -` X \<inter> space (restrict_space M (f -` \<Omega> \<inter> space M)))"
  proof (rule emeasure_distr)
    show "f \<in> restrict_space M (f -` \<Omega> \<inter> space M) \<rightarrow>\<^sub>M restrict_space N \<Omega>"
      by (rule measurable_restrict_space3) auto
  next
    from X show "X \<in> sets (restrict_space N \<Omega>)"
      by (simp add: sets_restrict_space)
  qed
  also have "\<dots> = emeasure M (f -` X \<inter> space (restrict_space M (f -` \<Omega> \<inter> space M)))"
  proof (rule emeasure_restrict_space)
    have "f -` (\<Omega> \<inter> space N) \<inter> space M \<in> sets M"
      by (rule measurable_sets[OF assms(1)]) auto
    also have "f -` (\<Omega> \<inter> space N) \<inter> space M = f -` \<Omega> \<inter> space M \<inter> space M"
      using assms(1) unfolding measurable_def by auto
    finally show "\<dots> \<in> sets M" .
  next
    show "f -` X \<inter> space (restrict_space M (f -` \<Omega> \<inter> space M)) \<subseteq> f -` \<Omega> \<inter> space M"
      by (auto simp: space_restrict_space)
  qed
  also have "f -` X \<inter> space (restrict_space M (f -` \<Omega> \<inter> space M)) = f -` X \<inter> space M"
    using X by (auto simp: space_restrict_space sets_restrict_space)
  also have "emeasure M \<dots> = emeasure (distr M N f) X"
    using X' by (subst emeasure_distr) (auto simp: sets_restrict_space)
  also have "\<dots> = emeasure (restrict_space (distr M N f) \<Omega>) X"
    using X by (subst emeasure_restrict_space) (auto simp: sets_restrict_space)
  finally show "emeasure (restrict_space (distr M N f) \<Omega>) X =
                emeasure (distr (restrict_space M (f -` \<Omega> \<inter> space M)) (restrict_space N \<Omega>) f) X" ..
qed (auto simp: sets_restrict_space emeasure_restrict_space emeasure_distr)


lemma pmfsr_not_None_measurable [measurable]:
  assumes "wf_pmfsr p"
  shows   "{bs. p bs \<noteq> None} \<in> sets coin_space"
proof -
  note [measurable] = measurable_pmfsr[OF assms]
  have "{bs. p bs \<noteq> None} = space coin_space - (p -` {None} \<inter> space coin_space)"
    by (auto simp: space_coin_space)
  also have "\<dots> \<in> sets coin_space"
    by measurable
  finally show ?thesis .
qed

lemma measure_pmfsr''_altdef:
  assumes "wf_pmfsr p"
  shows   "measure_pmfsr'' p =
           distr (restrict_space coin_space {bs. p bs \<noteq> None}) (count_space UNIV) ((fst \<circ> the) \<circ> p)"
proof (rule measure_eqI, goal_cases)
  case (2 X)
  have "emeasure (distr (restrict_space coin_space {bs. p bs \<noteq> None}) (count_space UNIV) (fst \<circ> the \<circ> p)) X =
        emeasure (restrict_space coin_space {bs. p bs \<noteq> None})
          ((fst \<circ> the \<circ> p) -` X \<inter> space (restrict_space coin_space {bs. p bs \<noteq> None}))"
  proof (rule emeasure_distr)
    show "fst \<circ> the \<circ> p \<in> restrict_space coin_space {bs. p bs \<noteq> None} \<rightarrow>\<^sub>M count_space UNIV"
    proof (rule measurable_comp)
      show "p \<in> restrict_space coin_space {bs. p bs \<noteq> None} \<rightarrow>\<^sub>M
                restrict_space (count_space UNIV) (range Some)"
        by (intro measurable_restrict_space3 measurable_pmfsr assms) auto
    qed auto
  qed auto
  also have "\<dots> = emeasure coin_space ((fst \<circ> the \<circ> p) -` X \<inter> {bs. p bs \<noteq> None})"
  proof (subst emeasure_restrict_space)
    show "{bs. p bs \<noteq> None} \<inter> space coin_space \<in> coin_space.events"
      by (intro sets.Int pmfsr_not_None_measurable assms) auto
  qed (auto simp: space_restrict_space space_coin_space)
  also have "(fst \<circ> the \<circ> p) -` X \<inter> {bs. p bs \<noteq> None} = (map_option fst \<circ> p) -` Some ` X"
    by (auto simp: space_restrict_space space_coin_space)
  
  also have "emeasure coin_space \<dots> = emeasure (measure_pmfsr'' p) X"
    using assms  by (simp add: emeasure_measure_pmfsr'' emeasure_measure_pmfsr)
  finally show ?case ..
qed (auto simp: measure_pmfsr''_def)

lemma prob_mono_pmfsr:
  assumes "wf_pmfsr r" "wf_pmfsr s" "ord_pmfsr r s"
  shows   "Sigma_Algebra.measure (measure_pmfsr'' r) X \<le> Sigma_Algebra.measure (measure_pmfsr'' s) X"
proof -
  have "coin_space.prob ((map_option fst \<circ> r) -` Some ` X) \<le>
        coin_space.prob ((map_option fst \<circ> s) -` Some ` X)"
  proof (rule coin_space.finite_measure_mono)
    show "(map_option fst \<circ> r) -` Some ` X \<subseteq> (map_option fst \<circ> s) -` Some ` X"
      using ord_pmfsrD[OF assms(3)]
      by (auto simp: map_option_case inj_image_mem_iff split: option.splits)
    show "(map_option fst \<circ> s) -` Some ` X \<in> coin_space.events"
      by (rule measurable_sets_space_UNIV[of _ _ "count_space UNIV"]
               measurable_comp[OF measurable_pmfsr] assms)+ (auto simp: space_coin_space)
  qed
  thus ?thesis
    using assms by (simp add: prob_measure_pmfsr'' prob_measure_pmfsr)
qed

lemma mono_measure_pmfsr'':
  assumes "wf_pmfsr r" "wf_pmfsr s" "ord_pmfsr r s"
  shows   "measure_pmfsr'' r \<le> measure_pmfsr'' s"
proof (rule less_eq_measure.intros(3))
  interpret r: subprob_space "measure_pmfsr'' r"
    by (rule subprob_space_measure_pmfsr'') fact
  interpret s: subprob_space "measure_pmfsr'' s"
    by (rule subprob_space_measure_pmfsr'') fact
  show "emeasure (measure_pmfsr'' r) \<le> emeasure (measure_pmfsr'' s)"
    using prob_mono_pmfsr[OF assms]
    by (intro le_funI) (simp add: r.emeasure_eq_measure s.emeasure_eq_measure)
qed (auto simp: measure_pmfsr''_def)

lemma Sup_Sup_ennreal: "(\<Squnion>x\<in>A. \<Squnion>(B x)) = \<Squnion>(\<Union>x\<in>A. B x :: ennreal set)"
  apply (rule antisym)
   apply (simp add: SUP_least SUP_upper Sup_subset_mono)
  apply (meson Sup_upper UN_iff complete_lattice_class.Sup_mono image_eqI)
  done

lemma spmf_of_pmfsr_bot [simp]: "spmf_of_pmfsr (\<lambda>_. None) = return_pmf None"
  sorry

lemma mylemma:
  assumes "Complete_Partial_Order.chain ord_pmfsr Y" "\<And>y. y \<in> Y \<Longrightarrow> wf_pmfsr y"
  assumes "finite B" "\<And>bs. bs \<in> B \<Longrightarrow> \<exists>p\<in>Y. p bs \<noteq> None"
  obtains p where "p \<in> Y" "\<And>bs. bs \<in> B \<Longrightarrow> p bs \<noteq> None"
  sorry

lemma cont_spmf_of_pmfsr:
  assumes "\<And>y. y \<in> Y \<Longrightarrow> wf_pmfsr y"
  assumes "Complete_Partial_Order.chain ord_pmfsr Y"
  shows   "spmf_of_pmfsr (lub_pmfsr Y) = lub_spmf (spmf_of_pmfsr ` Y)"
proof (cases "Y = {}")
  case True
  thus ?thesis
    by auto
next
  case False
  show ?thesis
  proof (rule spmf_eqI)
    fix x :: 'a

    define B :: "nat \<Rightarrow> bool list set"
      where "B = (\<lambda>n. {stake n bs |bs p. p \<in> Y \<and> p bs = Some (x, n)})"
    define B' where "B' = (\<lambda>n. \<Union>k\<le>n. stake k -` B k)"
    define A :: "(nat \<times> bool list) set"
      where "A = (SIGMA n:UNIV. B n)"
    have fin_B: "finite (B n)" for n
    proof (rule finite_subset)
      show "B n \<subseteq> {bs. length bs = n}"
        by (auto simp: B_def)
      show "finite {bs :: bool list. length bs = n}"
        using finite_lists_length_eq[of "UNIV :: bool set"] by simp
    qed

    have "countable A"
    proof (rule countable_subset)
      show "A \<subseteq> (SIGMA n:UNIV. {bs. length bs = n})"
        by (auto simp: A_def B_def)
      show "countable (SIGMA n:UNIV. {bs. length (bs :: bool list) = n})"
        by (intro countable_SIGMA) auto
    qed

    have "ennreal (spmf (spmf_of_pmfsr (lub_pmfsr Y)) x) = 
            emeasure coin_space ((map_option fst \<circ> lub_pmfsr Y) -` {Some x})"
      by (simp add: pmf.rep_eq prob_measure_pmfsr wf_lub_pmfsr assms
                    spmf_of_pmfsr.rep_eq coin_space.emeasure_eq_measure)
    also have "(map_option fst \<circ> lub_pmfsr Y) -` {Some x} = {bs |bs n. lub_pmfsr Y bs = Some (x, n)}"
      by auto
    also have "\<dots> = (\<Union>(n,bs')\<in>A. {bs. stake n bs = bs'})"
    proof (intro equalityI subsetI)
      fix bs assume "bs \<in> {bs |bs n. lub_pmfsr Y bs = Some (x, n)}"
      then obtain n where "lub_pmfsr Y bs = Some (x, n)"
        by blast
      thus "bs \<in> (\<Union>(n,bs')\<in>A. {bs. stake n bs = bs'})"
        by (elim lub_pmfsr_eq_SomeE) (auto simp: A_def B_def)
    next
      fix bs assume "bs \<in> (\<Union>(n,bs')\<in>A. {bs. stake n bs = bs'})"
      then obtain n bs' p where *: "p \<in> Y" "stake n bs = stake n bs'" "p bs' = Some (x, n)"
        by (auto simp: A_def eq_commute B_def)
      moreover from assms * have "wf_pmfsr p"
        by auto
      ultimately have "lub_pmfsr Y bs = Some (x, n)"
        using wf_pmfsrD[OF \<open>wf_pmfsr p\<close>, of bs' x n bs] assms
        by (intro lub_pmfsr_eq_SomeI'[of p]) auto
      thus "bs \<in> {bs |bs n. lub_pmfsr Y bs = Some (x, n)}"
        by simp
    qed
    also have "\<dots> = (\<Union>n. stake n -` B n)"
      by (auto simp: A_def)
    also have "\<dots> = (\<Union>n. B' n)"
      by (auto simp: B'_def)
    also have "emeasure coin_space (\<Union>n. B' n) = (\<Squnion>n. emeasure coin_space (B' n))"
    proof (rule SUP_emeasure_incseq [symmetric])
      show "incseq B'"
        unfolding B'_def by (force simp: incseq_def)
      show "range B' \<subseteq> coin_space.events"
        unfolding B'_def
        by (auto intro!: sets.countable_UN measurable_sets_space_UNIV[of _ _ "count_space UNIV"] 
                 simp: coin_space_def space_stream_space)
    qed
    finally have 1: "ennreal (spmf (spmf_of_pmfsr (lub_pmfsr Y)) x) = (\<Squnion>n. emeasure coin_space (B' n))" .

    (*

    also have "emeasure coin_space \<dots> = (\<Sum>n. emeasure coin_space (stake n -` B n))"
    proof (rule suminf_emeasure [symmetric])
      show "range (\<lambda>n. stake n -` B n) \<subseteq> coin_space.events"
        by (safe, rule measurable_sets_space_UNIV[of _ _ "count_space UNIV"])
           (auto simp: coin_space_def space_stream_space)
    next
      have "lub_pmfsr Y bs = Some (x, n)" if "stake n bs \<in> B n" for bs n
      proof -
        from that obtain p bs' where "p \<in> Y" "stake n bs = stake n bs'" "p bs' = Some (x, n)"
          by (auto simp: B_def)
        thus ?thesis
          using wf_pmfsrD[of p bs' x n bs] assms
          by (intro lub_pmfsr_eq_SomeI'[of p]) auto
      qed
      thus "disjoint_family (\<lambda>i. stake i -` B i)"
        unfolding disjoint_family_on_def 
        by (metis Int_emptyI option.inject prod.inject vimageE)
    qed
    also have "emeasure coin_space (stake n -` B n) = ennreal (card (B n) / 2 ^ n)" for n
      by (rule emeasure_coin_space_stake) (auto simp: B_def)
    hence "(\<Sum>n. emeasure coin_space (stake n -` B n)) = (\<Sum>n. ennreal (card (B n) / 2 ^ n))"
      by (simp only: )
    finally have "ennreal (spmf (spmf_of_pmfsr (lub_pmfsr Y)) x) =
                    (\<Sum>n. ennreal (real (card (B n)) / 2 ^ n))" .*)
 
    have "ennreal (spmf (lub_spmf (spmf_of_pmfsr ` Y)) x) =
          (\<Squnion>p\<in>Y. ennreal (spmf (spmf_of_pmfsr p) x))"
    proof (subst ennreal_spmf_lub_spmf)
      show "Complete_Partial_Order.chain (ord_spmf (=)) (spmf_of_pmfsr ` Y)"
        using assms(1,2) by (intro chain_imageI[OF assms(2)] mono_spmf_of_pmfsr) auto
    qed (use False in \<open>auto simp: image_image\<close>)
    also have "\<dots> = (\<Squnion>p\<in>Y. emeasure (measure_pmfsr'' p) {x})"
    proof (rule SUP_cong, goal_cases)
      case (2 p)
      have "ennreal (spmf (spmf_of_pmfsr p) x) = emeasure (measure_pmfsr p) {Some x}"
        using 2 by (metis assms(1) emeasure_pmf_single spmf_of_pmfsr.rep_eq)
      also have "{Some x} = Some ` {x}"
        by auto
      also have "emeasure (measure_pmfsr p) \<dots> = emeasure (measure_pmfsr'' p) {x}"
        using assms 2 by (simp add: emeasure_measure_pmfsr'')
      finally show ?case .
    qed auto
    also have "(\<lambda>p. emeasure (measure_pmfsr'' p) {x}) ` Y =
               (\<lambda>p. \<Squnion>n. emeasure coin_space (p -` (\<lambda>k. Some (x, k)) ` {..n})) ` Y"
    proof (intro image_cong, goal_cases)
      case (2 p)
      have "emeasure (measure_pmfsr'' p) {x} = emeasure coin_space ((map_option fst \<circ> p) -` {Some x})"
        using assms 2 by (simp add: emeasure_measure_pmfsr'' emeasure_measure_pmfsr)
      also have "(map_option fst \<circ> p) -` {Some x} = (\<Union>n. p -` (\<lambda>k. Some (x, k)) ` {..n})"
        by force
      also have "emeasure coin_space \<dots> =
                 (\<Squnion>n. emeasure coin_space (p -` (\<lambda>k. Some (x, k)) ` {..n}))"
      proof (rule SUP_emeasure_incseq [symmetric])
        show "range (\<lambda>i. p -` (\<lambda>k. Some (x, k)) ` {..i}) \<subseteq> coin_space.events"
          using assms 2
          by (auto intro!: measurable_sets_space_UNIV[of _ _ "count_space UNIV"]
                           measurable_pmfsr[of p] simp: space_coin_space)
        show "incseq (\<lambda>i. p -` (\<lambda>k. Some (x, k)) ` {..i})"
          unfolding incseq_def by auto
      qed
      finally show ?case .
    qed auto
    also have "\<Squnion>\<dots> = \<Squnion> (\<Union>p\<in>Y. range (\<lambda>n. emeasure coin_space (p -` (\<lambda>k. Some (x, k)) ` {..n})))"
      by (rule Sup_Sup_ennreal)
    also have "(\<Union>p\<in>Y. range (\<lambda>n. emeasure coin_space (p -` (\<lambda>k. Some (x, k)) ` {..n}))) =
               (\<Union>n. \<Union>p\<in>Y. {emeasure coin_space (p -` (\<lambda>k. Some (x, k)) ` {..n})})"
      by auto
    also have "\<Squnion>\<dots> = (\<Squnion>n. \<Squnion>p\<in>Y. emeasure coin_space (p -` (\<lambda>k. Some (x, k)) ` {..n}))"
      by (subst Sup_Sup_ennreal, rule arg_cong[of _ _ Sup]) auto
    also have "\<dots> = (\<Squnion>n. emeasure coin_space (B' n))"
    proof (intro arg_cong[of _ _ Sup] image_cong, goal_cases)
      case (2 n)
      define C where "C = (\<lambda>p. {bs. p (bs @- sconst False) = Some (x, length bs) \<and> length bs \<le> n})"
      have "C ` Y \<subseteq> Pow {bs. length bs \<le> n}"
        by (auto simp: C_def)
      hence fin: "finite (C ` Y)"
        apply (rule finite_subset)
        apply simp
        using finite_lists_length_le[of "UNIV :: bool set" n]
        apply simp
        done

      have "(\<Squnion>p\<in>Y. emeasure coin_space (p -` (\<lambda>k. Some (x, k)) ` {..n})) =
            \<Squnion>(emeasure coin_space ` (\<lambda>p. (p -` (\<lambda>k. Some (x, k)) ` {..n})) ` Y)"
        by (simp add: image_image o_def)
      also have "(\<lambda>p. (p -` (\<lambda>k. Some (x, k)) ` {..n})) ` Y = (\<lambda>p. \<Union>bs\<in>C p. stake (length bs) -` {bs}) ` Y"
        apply (intro image_cong refl)
        apply (auto simp: C_def)
        using assms(1)
         apply (metis dual_order.refl length_stake stake_shift_small take_all wf_pmfsrD)
        by (smt (verit, ccfv_SIG) assms(1) atMost_iff dual_order.refl image_eqI stake_shift_small take_all wf_pmfsrD)
      also have "(emeasure coin_space ` (\<lambda>p. \<Union>bs\<in>C p. stake (length bs) -` {bs}) ` Y) =
                 (\<lambda>B. emeasure coin_space (\<Union>bs\<in>B. stake (length bs) -` {bs})) ` C ` Y"
        by (simp add: image_image o_def)
      also have "\<Squnion>\<dots> = Max \<dots>"
        using \<open>Y \<noteq> {}\<close> by (intro Max_Sup [symmetric] finite_imageI[OF fin]) auto
      also have "\<dots> = emeasure coin_space (B' n)"
      proof (rule Max_eqI, goal_cases)
        case (2 u)
        then obtain p where p: "p \<in> Y" and
          [simp]: "u = emeasure coin_space (\<Union>bs\<in>C p. stake (length bs) -` {bs})"
          by auto
        have "emeasure coin_space (\<Union>bs\<in>C p. stake (length bs) -` {bs}) \<le> emeasure coin_space (B' n)"
          using p
          apply (intro emeasure_mono)
          subgoal
           apply (auto simp: B'_def C_def B_def)
          subgoal for bs bs'
            apply (rule bexI[of _ "length bs'"])
             apply (rule exI[of _ bs])
             apply auto
            apply (rule exI[of _ p])
            apply auto
            using assms(1)[of p] wf_pmfsrD[of p "bs' @- sconst False" x "length bs'" bs]
            apply auto
            done
          done
        unfolding B'_def
        apply (intro sets.countable_UN)
        apply safe
        apply (rule measurable_sets_space_UNIV[of _ _ "count_space UNIV"])
          apply (auto simp: space_coin_space coin_space_def space_stream_space)
        done
        thus ?case
          by simp
      next
        case 3
        obtain p where p: "p \<in> Y" "B' n = {bs |bs k. p bs = Some (x, k) \<and> k \<le> n}"
          sorry
        thus ?case
          unfolding C_def
          apply (auto)
          apply (rule image_eqI[of _ _ "C p"])
           apply (rule arg_cong[of _ _ "emeasure coin_space"])
           apply (simp add: p)
           apply (simp add: C_def)
           defer
          subgoal
            apply (rule image_eqI[of _ _ p])
            defer
             apply simp
            unfolding C_def
            apply auto
            done
          apply safe
           apply auto []
          subgoal for bs k
            apply (rule exI[of _ "stake k bs"])
            apply auto
            using assms
            by (metis dual_order.refl length_stake p(1) stake_sdrop stake_shift_small wf_pmfsrD)
          subgoal for bs bs'
            apply (rule exI[of _ "length bs'"])
            apply auto
            by (metis assms(1) dual_order.refl p(1) stake_shift_small take_all wf_pmfsrD)
          done
      qed (use fin in auto)
      finally show ?case .
    qed auto

    also note 1 [symmetric]
    finally show "spmf (spmf_of_pmfsr (lub_pmfsr Y)) x = spmf (lub_spmf (spmf_of_pmfsr ` Y)) x"
      by simp
  qed
qed
  

      

      find_theorems "Sup (\<Union> _)"
      find_theorems 

      find_theorems "emeasure _ (\<Union>_)" incseq
    also have "\<dots> = (\<lambda>p. emeasure coin_space ((map_option fst \<circ> p) -` {Some x})) ` Y"

    also have "\<dots> = emeasure (\<Squnion>p\<in>Y. measure_pmfsr'' p) {x}"
    proof (subst emeasure_SUP_chain [symmetric])
      show "sets (measure_pmfsr'' p) = sets (count_space UNIV)" for p :: "'a pmfsr"
        by (simp add: measure_pmfsr''_def)
      show "Complete_Partial_Order.chain (\<le>) (measure_pmfsr'' ` Y)"
        using assms by (intro chain_imageI[OF assms(2)] mono_measure_pmfsr'') auto
    qed (use False in auto)
    
    also 
    
    

    also have "\<dots> = (\<Squnion>p\<in>Y. emeasure coin_space ((map_option fst \<circ> p) -` {Some x}))"
    proof (intro SUP_cong refl)
      find_theorems "Sup ((\<lambda>x. (\<Sum>_. _)) ` _)"

    also have "\<dots> = T"
      find_theorems lub_spmf Complete_Partial_Order.chain Sigma_Algebra.measure
      find_theorems "emeasure _ (\<Union>_\<in>_. _)" "Sup :: ennreal set \<Rightarrow> ennreal"
      
      

    find_theorems "spmf (lub_spmf _) _"
  

  have "measure_pmf (spmf_of_pmfsr (lub_pmfsr Y)) = measure_pmf (lub_spmf (spmf_of_pmfsr ` Y))"
  proof -
    

  using assms
  apply (auto simp: pmf.rep_eq spmf_of_pmfsr.rep_eq wf_lub_pmfsr)
  





typedef 'a pmfs = "{r :: 'a pmfsr. wf_pmfsr r}"
proof -
  obtain x :: 'a where True
    by auto
  show "\<exists>r::'a pmfsr. r \<in> {r. wf_pmfsr r}"
    by (rule exI[of _ "return_pmfsr x"]) (auto intro: wf_return_pmfsr)
qed

setup_lifting type_definition_pmfs

lift_definition run_pmfs :: "'a pmfs \<Rightarrow> bool stream \<Rightarrow> 'a option" is
  "\<lambda>r bs. map_option fst (r bs)" .

lift_definition run_pmfs' :: "'a pmfs \<Rightarrow> bool stream \<Rightarrow> ('a \<times> nat) option" is
  "\<lambda>r. r" .

lift_definition return_pmfs :: "'a \<Rightarrow> 'a pmfs" is return_pmfsr
  by (rule wf_return_pmfsr)

lift_definition coin_pmfs :: "bool pmfs" is coin_pmfsr
  by (rule wf_coin_pmfsr)

lift_definition bind_pmfs :: "'a pmfs \<Rightarrow> ('a \<Rightarrow> 'b pmfs) \<Rightarrow> 'b pmfs" is bind_pmfsr
  by (rule wf_bind_pmfsr)

lift_definition loss_pmfs :: "'a pmfs \<Rightarrow> real" is loss_pmfsr .

lift_definition consumption_pmfs :: "'a pmfs \<Rightarrow> nat pmfs" is consumption_pmfsr
  by (rule wf_consumption_pmfsr)


adhoc_overloading Monad_Syntax.bind bind_pmfs

lift_definition map_pmfs :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pmfs \<Rightarrow> 'b pmfs" is map_pmfsr
  by (rule wf_map_pmfsr)

lift_definition range_pmfs :: "'a pmfs \<Rightarrow> 'a set" is range_pmfsr .

lift_definition spmf_of_pmfs :: "'a pmfs \<Rightarrow> 'a spmf" is spmf_of_pmfsr .

lift_definition bot_pmfs :: "'a pmfs" is "\<lambda>_. None" by auto

primrec replicate_pmfs :: "nat \<Rightarrow> 'a pmfs \<Rightarrow> 'a list pmfs" where
  "replicate_pmfs 0 r = return_pmfs []"
| "replicate_pmfs (Suc n) r = do {x \<leftarrow> r; map_pmfs (\<lambda>xs. x # xs) (replicate_pmfs n r)}"

lemma map_pmfs_id [simp]: "map_pmfs id r = r"
  by transfer (rule map_pmfsr_id)

lemma map_pmfs_id' [simp]: "map_pmfs (\<lambda>x. x) r = r"
  by transfer (rule map_pmfsr_id')

lemma map_pmfs_return [simp]: "map_pmfs f (return_pmfs x) = return_pmfs (f x)"
  by transfer auto

lemma map_pmfs_comp: "map_pmfs (f \<circ> g) r = map_pmfs f (map_pmfs g r)"
  by transfer (rule map_pmfsr_comp)

lemma map_pmfs_conv_bind_pmfs: "map_pmfs f r = bind_pmfs r (\<lambda>x. return_pmfs (f x))"
  by transfer (rule map_pmfsr_conv_bind_pmfsr)

lemma bind_return_pmfs': "bind_pmfs r return_pmfs = r"
  by transfer (rule bind_return_pmfsr')

lemma bind_return_pmfs: "bind_pmfs (return_pmfs x) r = r x"
  by transfer (rule bind_return_pmfsr)

lemma bind_assoc_pmfs: "(A :: 'a pmfs) \<bind> B \<bind> C = A \<bind> (\<lambda>x. B x \<bind> C)"
  by transfer (rule bind_assoc_pmfsr)  

lemma bind_pmfs_cong:
   "r = r' \<Longrightarrow> (\<And>x. x \<in> range_pmfs r \<Longrightarrow> f x = f' x) \<Longrightarrow> bind_pmfs r f = bind_pmfs r' f'"
  by transfer (use bind_pmfsr_cong in blast)

lemma replicate_pmfs_1 [simp]: "replicate_pmfs (Suc 0) r = map_pmfs (\<lambda>x. [x]) r"
  by (simp add: bind_return_pmfs' flip: map_pmfs_conv_bind_pmfs)

lemma weight_pmfs: "weight_spmf (spmf_of_pmfs r) = 1 - loss_pmfs r"
  by transfer (simp add: weight_pmfsr)

lemma loss_pmfs_altdef: "loss_pmfs r = pmf (spmf_of_pmfs r) None"
  by transfer (auto simp: loss_pmfsr_altdef)

lemma loss_pmfs_01: "loss_pmfs r \<in> {0..1}"
  unfolding loss_pmfs_altdef by (simp add: pmf_le_1)


lemma spmf_of_return_pmfs [simp]: "spmf_of_pmfs (return_pmfs x) = return_spmf x"
  by transfer simp

lemma spmf_of_coin_pmfs [simp]: "spmf_of_pmfs coin_pmfs = coin_spmf"
  by transfer simp

lemma spmf_of_bind_pmfs [simp]: "spmf_of_pmfs (r \<bind> f) = spmf_of_pmfs r \<bind> (spmf_of_pmfs \<circ> f)"
  by transfer (simp add: spmf_of_bind_pmfsr)

lemma spmf_of_map_pmfs [simp]: "spmf_of_pmfs (map_pmfs f r) = map_spmf f (spmf_of_pmfs r)"
  by transfer (simp add: spmf_of_map_pmfsr)

definition replicate_spmf where "replicate_spmf n p = map_pmf those (replicate_pmf n p)"

lemma replicate_spmf_0 [simp]: "replicate_spmf 0 p = return_spmf []"
  by (auto simp: replicate_spmf_def)

lemma replicate_spmf_Suc [simp]:
  "replicate_spmf (Suc n) p = do {x \<leftarrow> p; map_spmf (\<lambda>xs. x # xs) (replicate_spmf n p)}"
  by (auto simp: replicate_spmf_def map_bind_pmf bind_spmf_def pmf.map_comp o_def
           intro!: bind_pmf_cong split: option.splits simp flip: map_pmf_def)

lemma spmf_of_replicate_pmfs [simp]:
  "spmf_of_pmfs (replicate_pmfs n r) = replicate_spmf n (spmf_of_pmfs r)"
  by (induction n) (auto simp: o_def)


lemma loss_return_pmfs [simp]: "loss_pmfs (return_pmfs x) = 0"
  by transfer auto

lemma loss_coin_pmfs [simp]: "loss_pmfs (coin_pmfs ) = 0"
  by transfer auto

lemma loss_bind_pmfs:
  "loss_pmfs (r \<bind> f) = loss_pmfs r + (LINT x|measure_spmf (spmf_of_pmfs r). loss_pmfs (f x))"
  by transfer (auto simp: loss_bind_pmfsr)

lemma loss_map_pmfs [simp]: "loss_pmfs (map_pmfs f r) = loss_pmfs r"
  by transfer auto

lemma loss_replicate_pmfs: "loss_pmfs (replicate_pmfs n r) = 1 - (1 - loss_pmfs r) ^ n"
proof (induction n)
  case (Suc n)
  show "loss_pmfs (replicate_pmfs (Suc n) r) = 1 - (1 - loss_pmfs r) ^ Suc n"
    by (simp add: Suc loss_bind_pmfs weight_pmfs algebra_simps)
qed auto


lift_definition ord_pmfs :: "'a pmfs \<Rightarrow> 'a pmfs \<Rightarrow> bool" is ord_pmfsr .

lift_definition lub_pmfs :: "'a pmfs set \<Rightarrow> 'a pmfs" is
  "\<lambda>X. if Complete_Partial_Order.chain ord_pmfsr X then lub_pmfsr X else (\<lambda>_. None)"
  by (auto intro: wf_lub_pmfsr)

lemma lub_pmfs_empty [simp]: "lub_pmfs {} = bot_pmfs"
  by transfer auto

lemma lub_pmfs_const [simp]: "lub_pmfs {r} = r"
  by transfer (auto simp: Complete_Partial_Order.chain_def pmfsr.leq_refl)

lemma bot_pmfs_is_least [simp, intro]: "ord_pmfs bot_pmfs r"
  by transfer (auto simp: ord_pmfsr_def)

lemma partial_function_definitions_pmfs: 
  "partial_function_definitions ord_pmfs lub_pmfs"
  (is "partial_function_definitions ?R _")
proof
  fix x show "?R x x"
    by transfer (rule pmfsr.leq_refl)
next
  fix x y z
  assume "?R x y" "?R y z"
  thus "?R x z"
    by transfer (rule pmfsr.leq_trans)    
next
  fix x y
  assume "?R x y" "?R y x"
  thus "x = y"
    by transfer (rule pmfsr.leq_antisym)
next
  fix Y r
  assume "Complete_Partial_Order.chain ?R Y" "r \<in> Y"
  thus "?R r (lub_pmfs Y)"
    by transfer (use pmfsr.lub_upper in auto)
next
  fix Y r
  assume "Complete_Partial_Order.chain ?R Y" "\<And>r'. r' \<in> Y \<Longrightarrow> ?R r' r"
  thus "?R (lub_pmfs Y) r"
    by transfer (use pmfsr.lub_least in auto)
qed

lemma ccpo_pmfs: "class.ccpo lub_pmfs ord_pmfs (mk_less ord_pmfs)"
  by (rule ccpo partial_function_definitions_pmfs)+

interpretation pmfs: partial_function_definitions "ord_pmfs" "lub_pmfs"
  rewrites "lub_pmfs {} \<equiv> bot_pmfs"
  by (rule partial_function_definitions_pmfs) simp


declaration \<open>Partial_Function.init "pmfsr" \<^term>\<open>pmfsr.fixp_fun\<close>
  \<^term>\<open>pmfsr.mono_body\<close> @{thm pmfsr.fixp_rule_uc} @{thm pmfsr.fixp_induct_uc}
  NONE\<close>

declare pmfsr.leq_refl[simp]
declare admissible_leI[OF ccpo_pmfsr, cont_intro]

abbreviation "mono_pmfsr \<equiv> monotone (fun_ord ord_pmfsr) ord_pmfsr"

lemma bind_pmfsr_mono':
  assumes fg: "ord_pmfsr f g"
  and hk: "\<And>x :: 'a. ord_pmfsr (h x) (k x)"
  shows "ord_pmfsr (bind_pmfsr f h) (bind_pmfsr g k)"
  unfolding bind_pmfsr_def using assms
  apply (auto simp: ord_pmfsr_def rel_fun_def Option_bind_conv_case split: option.splits)
     apply (metis ord_option_eq_simps(2))
    apply (metis old.prod.inject option.discI option.sel ord_option_eq_simps(2))
   apply (metis Pair_inject option.inject ord_option_eq_simps(2))
  apply (metis fst_conv option.sel ord_option_eq_simps(2) snd_conv)
  done

lemma bind_pmfsr_mono [partial_function_mono]:
  assumes mf: "mono_pmfsr B" and mg: "\<And>y. mono_pmfsr (\<lambda>f. C y f)"
  shows "mono_pmfsr (\<lambda>f. bind_pmfsr (B f) (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b pmfsr"
  assume fg: "fun_ord ord_pmfsr f g"
  with mf have "ord_pmfsr (B f) (B g)" by (rule monotoneD[of _ _ _ f g])
  moreover from mg have "\<And>y'. ord_pmfsr (C y' f) (C y' g)"
    by (rule monotoneD) (rule fg)
  ultimately show "ord_pmfsr (bind_pmfsr (B f) (\<lambda>y. C y f)) (bind_pmfsr (B g) (\<lambda>y'. C y' g))"
    by (rule bind_pmfsr_mono')
qed

lemma monotone_bind_pmfsr1: "monotone ord_pmfsr ord_pmfsr (\<lambda>y. bind_pmfsr y g)"
  by (rule monotoneI) (simp add: bind_pmfsr_mono')

lemma monotone_bind_pmfsr2:
  assumes g: "\<And>x. monotone ord ord_pmfsr (\<lambda>y. g y x)"
  shows "monotone ord ord_pmfsr (\<lambda>y. bind_pmfsr p (g y))"
  by (rule monotoneI) (auto intro: bind_pmfsr_mono' monotoneD[OF g])

lemma bind_lub_pmfsr:
  assumes chain: "Complete_Partial_Order.chain ord_pmfsr Y"
  shows "bind_pmfsr (lub_pmfsr Y) f = lub_pmfsr ((\<lambda>p. bind_pmfsr p f) ` Y)" (is "?lhs = ?rhs")
  sorry
(*
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have chain': "Complete_Partial_Order.chain (\<le>) ((\<lambda>p x. ennreal (spmf p x * spmf (f x) i)) ` Y)"
      using chain by(rule chain_imageI)(auto simp add: le_fun_def dest: ord_spmf_eq_leD intro: mult_right_mono)
    have chain'': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. p \<bind> f) ` Y)"
      using chain by(rule chain_imageI)(auto intro!: monotoneI bind_spmf_mono' ord_spmf_reflI)
    let ?M = "count_space (set_spmf (lub_spmf Y))"
    have "ennreal (spmf ?lhs i) = \<integral>\<^sup>+ x. ennreal (spmf (lub_spmf Y) x) * ennreal (spmf (f x) i) \<partial>?M"
      by(auto simp add: ennreal_spmf_lub_spmf ennreal_spmf_bind nn_integral_measure_spmf')
    also have "\<dots> = \<integral>\<^sup>+ x. (SUP p\<in>Y. ennreal (spmf p x * spmf (f x) i)) \<partial>?M"
      by(subst ennreal_spmf_lub_spmf[OF chain Y])(subst SUP_mult_right_ennreal, simp_all add: ennreal_mult Y)
    also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ x. ennreal (spmf p x * spmf (f x) i) \<partial>?M)"
      using Y chain' by(rule nn_integral_monotone_convergence_SUP_countable) simp
    also have "\<dots> = (SUP p\<in>Y. ennreal (spmf (bind_spmf p f) i))"
      by(auto simp add: ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_indicator set_lub_spmf[OF chain] in_set_spmf_iff_spmf ennreal_mult intro!: arg_cong [of _ _ Sup] image_cong nn_integral_cong split: split_indicator)
    also have "\<dots> = ennreal (spmf ?rhs i)" using chain'' by(simp add: ennreal_spmf_lub_spmf Y image_comp)
    finally show "spmf ?lhs i = spmf ?rhs i" by simp
  qed
qed simp
*)

(*
lemma map_lub_spmf:
  "Complete_Partial_Order.chain (ord_spmf (=)) Y
  \<Longrightarrow> map_spmf f (lub_spmf Y) = lub_spmf (map_spmf f ` Y)"
unfolding map_spmf_conv_bind_spmf[abs_def] by(simp add: bind_lub_spmf o_def)
*)

lemma mcont_bind_pmfsr1: "mcont lub_pmfsr ord_pmfsr lub_pmfsr ord_pmfsr (\<lambda>y. bind_pmfsr y f)"
  using monotone_bind_pmfsr1 by (rule mcontI) (rule contI, simp add: bind_lub_pmfsr)

lemma bind_lub_pmfsr2:
  assumes chain: "Complete_Partial_Order.chain ord Y"
  and g: "\<And>y. monotone ord ord_pmfsr (g y)"
  shows "bind_pmfsr x (\<lambda>y. lub_pmfsr (g y ` Y)) = lub_pmfsr ((\<lambda>p. bind_pmfsr x (\<lambda>y. g y p)) ` Y)"
  (is "?lhs = ?rhs")
  sorry
(*
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have chain': "\<And>y. Complete_Partial_Order.chain (ord_spmf (=)) (g y ` Y)"
      using chain g[THEN monotoneD] by(rule chain_imageI)
    have chain'': "Complete_Partial_Order.chain (\<le>) ((\<lambda>p y. ennreal (spmf x y * spmf (g y p) i)) ` Y)"
      using chain by(rule chain_imageI)(auto simp add: le_fun_def dest: ord_spmf_eq_leD monotoneD[OF g] intro!: mult_left_mono)
    have chain''': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. bind_spmf x (\<lambda>y. g y p)) ` Y)"
      using chain by(rule chain_imageI)(rule monotone_bind_spmf2[OF g, THEN monotoneD])

    have "ennreal (spmf ?lhs i) = \<integral>\<^sup>+ y. (SUP p\<in>Y. ennreal (spmf x y * spmf (g y p) i)) \<partial>count_space (set_spmf x)"
      by(simp add: ennreal_spmf_bind ennreal_spmf_lub_spmf[OF chain'] Y nn_integral_measure_spmf' SUP_mult_left_ennreal ennreal_mult image_comp)
    also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ y. ennreal (spmf x y * spmf (g y p) i) \<partial>count_space (set_spmf x))"
      unfolding nn_integral_measure_spmf' using Y chain''
      by(rule nn_integral_monotone_convergence_SUP_countable) simp
    also have "\<dots> = (SUP p\<in>Y. ennreal (spmf (bind_spmf x (\<lambda>y. g y p)) i))"
      by(simp add: ennreal_spmf_bind nn_integral_measure_spmf' ennreal_mult)
    also have "\<dots> = ennreal (spmf ?rhs i)" using chain'''
      by(auto simp add: ennreal_spmf_lub_spmf Y image_comp)
    finally show "spmf ?lhs i = spmf ?rhs i" by simp
  qed
qed simp
*)

lemma mcont_bind_pmfsr [cont_intro]:
  assumes f: "mcont luba orda lub_pmfsr ord_pmfsr f"
  and g: "\<And>y. mcont luba orda lub_pmfsr ord_pmfsr (g y)"
  shows "mcont luba orda lub_pmfsr ord_pmfsr (\<lambda>x. bind_pmfsr (f x) (\<lambda>y. g y x))"
proof(rule pmfsr.mcont2mcont'[OF _ _ f])
  fix z
  show "mcont lub_pmfsr ord_pmfsr lub_pmfsr ord_pmfsr (\<lambda>x. bind_pmfsr x (\<lambda>y. g y z))"
    by(rule mcont_bind_pmfsr1)
next
  fix x
  let ?f = "\<lambda>z. bind_pmfsr x (\<lambda>y. g y z)"
  have "monotone orda ord_pmfsr ?f" using mcont_mono[OF g] by(rule monotone_bind_pmfsr2)
  moreover have "cont luba orda lub_pmfsr ord_pmfsr ?f"
  proof(rule contI)
    fix Y
    assume chain: "Complete_Partial_Order.chain orda Y" and Y: "Y \<noteq> {}"
    have "bind_pmfsr x (\<lambda>y. g y (luba Y)) = bind_pmfsr x (\<lambda>y. lub_pmfsr (g y ` Y))"
      by (rule bind_pmfsr_cong) (simp_all add: mcont_contD[OF g chain Y])
    also have "\<dots> = lub_pmfsr ((\<lambda>p. bind_pmfsr x (\<lambda>y. g y p)) ` Y)" using chain
      by (rule bind_lub_pmfsr2)(rule mcont_mono[OF g])
    finally show "bind_pmfsr x (\<lambda>y. g y (luba Y)) = \<dots>" .
  qed
  ultimately show "mcont luba orda lub_pmfsr ord_pmfsr ?f" by(rule mcontI)
qed


lemma map_pmfsr_mono [partial_function_mono]: "mono_pmfsr B \<Longrightarrow> mono_pmfsr (\<lambda>g. map_pmfsr f (B g))"
  unfolding map_pmfsr_conv_bind_pmfsr by(rule bind_pmfsr_mono) simp_all

lemma mcont_map_pmfsr [cont_intro]:
  "mcont luba orda lub_pmfsr ord_pmfsr g
  \<Longrightarrow> mcont luba orda lub_pmfsr ord_pmfsr (\<lambda>x. map_pmfsr f (g x))"
  unfolding map_pmfsr_conv_bind_pmfsr by (rule mcont_bind_pmfsr) simp_all


lemma monotone_set_pmfsr: "monotone ord_pmfsr (\<subseteq>) range_pmfsr"
  apply (rule monotoneI)
  apply (auto simp: ord_pmfsr_def rel_fun_def range_pmfsr_def)
  by (metis in_range_pmfsrI ord_option_eq_simps(2) range_pmfsr_def)

lemma cont_set_pmfsr: "cont lub_pmfsr ord_pmfsr Union (\<subseteq>) range_pmfsr"
  apply (rule contI)
  apply (auto simp: ord_pmfsr_def rel_fun_def range_pmfsr_def)
   apply (metis in_range_pmfsrI lub_pmfsr_eq_SomeE range_pmfsr_def)
  oops


lemma mcont2mcont_set_pmfsr[THEN mcont2mcont, cont_intro]:
  shows mcont_set_pmfsr: "mcont lub_pmfsr ord_pmfsr Union (\<subseteq>) range_pmfsr"
  oops
(*
by(rule mcontI monotone_set_pmfsr cont_set_pmfsr)+
*)



(*
  NB: if a recursively defined sampler (PMFS) is lossless, then due to the monotonicity of
  spmf_of_pmfs, the SPMF defined by the equivalent recurrence is unique, lossless, and equals the 
  one generated by the sampler.

  At least I think so.
*)
lemma ord_spmf_eq_and_weight_spmf_1_imp_eq:
  assumes "ord_spmf (=) p q" and "weight_spmf p = 1"
  shows   "p = q"
proof (rule pmf_eqI)
  fix x :: "'a option"
  show "pmf p x = pmf q x"
  proof (cases x)
    case None
    thus ?thesis
      using assms apply (simp add: pmf_None_eq_weight_spmf)
      by (metis ennreal_le_iff measure_nonneg measure_spmf.emeasure_eq_measure 
                measure_spmf.subprob_measure_le_1 ord_spmf_eqD_emeasure order_antisym_conv
                space_measure_spmf)
  next
    case [simp]: (Some y)
    show ?thesis
      using assms
      apply auto
      by (smt (verit) ord_option.cases pmf.rel_eq pmf.rel_mono_strong pmf_None_eq_weight_spmf set_pmf_iff)
  qed
qed

lemma
  assumes "weight_spmf p = weight_spmf q" "ord_spmf (=) p q"
  shows   "p = q"
  oops

lemma mono_spmf_of_pmfsr:
  assumes "ord_pmfsr r r'" "wf_pmfsr r" "wf_pmfsr r'"
  shows   "ord_spmf (=) (spmf_of_pmfsr r) (spmf_of_pmfsr r')"
  sorry

lemma mono_spmf_of_pmfs:
  assumes "ord_pmfs r r'"
  shows   "ord_spmf (=) (spmf_of_pmfs r) (spmf_of_pmfs r')"
  using assms by transfer (rule mono_spmf_of_pmfsr)




declaration \<open>Partial_Function.init "pmfs" \<^term>\<open>pmfs.fixp_fun\<close>
  \<^term>\<open>pmfs.mono_body\<close> @{thm pmfs.fixp_rule_uc} @{thm pmfs.fixp_induct_uc}
  NONE\<close>

declare pmfs.leq_refl[simp]
declare admissible_leI[OF ccpo_pmfs, cont_intro]

abbreviation "mono_pmfs \<equiv> monotone (fun_ord ord_pmfs) ord_pmfs"

lemma bind_pmfs_mono':
  assumes fg: "ord_pmfs f g"
  and hk: "\<And>x :: 'a. ord_pmfs (h x) (k x)"
shows "ord_pmfs (bind_pmfs f h) (bind_pmfs g k)"
  using assms by transfer (use bind_pmfsr_mono' in blast)

lemma bind_pmfs_mono [partial_function_mono]:
  assumes mf: "mono_pmfs B" and mg: "\<And>y. mono_pmfs (\<lambda>f. C y f)"
  shows "mono_pmfs (\<lambda>f. bind_pmfs (B f) (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b pmfs"
  assume fg: "fun_ord ord_pmfs f g"
  with mf have "ord_pmfs (B f) (B g)" by (rule monotoneD[of _ _ _ f g])
  moreover from mg have "\<And>y'. ord_pmfs (C y' f) (C y' g)"
    by (rule monotoneD) (rule fg)
  ultimately show "ord_pmfs (bind_pmfs (B f) (\<lambda>y. C y f)) (bind_pmfs (B g) (\<lambda>y'. C y' g))"
    by (rule bind_pmfs_mono')
qed

lemma monotone_bind_pmfs1: "monotone ord_pmfs ord_pmfs (\<lambda>y. bind_pmfs y g)"
  by (rule monotoneI) (simp add: bind_pmfs_mono')

lemma monotone_bind_pmfs2:
  assumes g: "\<And>x. monotone ord ord_pmfs (\<lambda>y. g y x)"
  shows "monotone ord ord_pmfs (\<lambda>y. bind_pmfs p (g y))"
  by (rule monotoneI) (auto intro: bind_pmfs_mono' monotoneD[OF g])

lemma bind_lub_pmfs:
  assumes chain: "Complete_Partial_Order.chain ord_pmfs Y"
  shows "bind_pmfs (lub_pmfs Y) f = lub_pmfs ((\<lambda>p. bind_pmfs p f) ` Y)" (is "?lhs = ?rhs")
  sorry
(*
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have chain': "Complete_Partial_Order.chain (\<le>) ((\<lambda>p x. ennreal (spmf p x * spmf (f x) i)) ` Y)"
      using chain by(rule chain_imageI)(auto simp add: le_fun_def dest: ord_spmf_eq_leD intro: mult_right_mono)
    have chain'': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. p \<bind> f) ` Y)"
      using chain by(rule chain_imageI)(auto intro!: monotoneI bind_spmf_mono' ord_spmf_reflI)
    let ?M = "count_space (set_spmf (lub_spmf Y))"
    have "ennreal (spmf ?lhs i) = \<integral>\<^sup>+ x. ennreal (spmf (lub_spmf Y) x) * ennreal (spmf (f x) i) \<partial>?M"
      by(auto simp add: ennreal_spmf_lub_spmf ennreal_spmf_bind nn_integral_measure_spmf')
    also have "\<dots> = \<integral>\<^sup>+ x. (SUP p\<in>Y. ennreal (spmf p x * spmf (f x) i)) \<partial>?M"
      by(subst ennreal_spmf_lub_spmf[OF chain Y])(subst SUP_mult_right_ennreal, simp_all add: ennreal_mult Y)
    also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ x. ennreal (spmf p x * spmf (f x) i) \<partial>?M)"
      using Y chain' by(rule nn_integral_monotone_convergence_SUP_countable) simp
    also have "\<dots> = (SUP p\<in>Y. ennreal (spmf (bind_spmf p f) i))"
      by(auto simp add: ennreal_spmf_bind nn_integral_measure_spmf nn_integral_count_space_indicator set_lub_spmf[OF chain] in_set_spmf_iff_spmf ennreal_mult intro!: arg_cong [of _ _ Sup] image_cong nn_integral_cong split: split_indicator)
    also have "\<dots> = ennreal (spmf ?rhs i)" using chain'' by(simp add: ennreal_spmf_lub_spmf Y image_comp)
    finally show "spmf ?lhs i = spmf ?rhs i" by simp
  qed
qed simp
*)

(*
lemma map_lub_spmf:
  "Complete_Partial_Order.chain (ord_spmf (=)) Y
  \<Longrightarrow> map_spmf f (lub_spmf Y) = lub_spmf (map_spmf f ` Y)"
unfolding map_spmf_conv_bind_spmf[abs_def] by(simp add: bind_lub_spmf o_def)
*)
                   
lemma mcont_bind_pmfs1: "mcont lub_pmfs ord_pmfs lub_pmfs ord_pmfs (\<lambda>y. bind_pmfs y f)"
  using monotone_bind_pmfs1 by (rule mcontI) (rule contI, simp add: bind_lub_pmfs)

lemma bind_lub_pmfs2:
  assumes chain: "Complete_Partial_Order.chain ord Y"
  and g: "\<And>y. monotone ord ord_pmfs (g y)"
  shows "bind_pmfs x (\<lambda>y. lub_pmfs (g y ` Y)) = lub_pmfs ((\<lambda>p. bind_pmfs x (\<lambda>y. g y p)) ` Y)"
  (is "?lhs = ?rhs")
  sorry
(*
proof(cases "Y = {}")
  case Y: False
  show ?thesis
  proof(rule spmf_eqI)
    fix i
    have chain': "\<And>y. Complete_Partial_Order.chain (ord_spmf (=)) (g y ` Y)"
      using chain g[THEN monotoneD] by(rule chain_imageI)
    have chain'': "Complete_Partial_Order.chain (\<le>) ((\<lambda>p y. ennreal (spmf x y * spmf (g y p) i)) ` Y)"
      using chain by(rule chain_imageI)(auto simp add: le_fun_def dest: ord_spmf_eq_leD monotoneD[OF g] intro!: mult_left_mono)
    have chain''': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. bind_spmf x (\<lambda>y. g y p)) ` Y)"
      using chain by(rule chain_imageI)(rule monotone_bind_spmf2[OF g, THEN monotoneD])

    have "ennreal (spmf ?lhs i) = \<integral>\<^sup>+ y. (SUP p\<in>Y. ennreal (spmf x y * spmf (g y p) i)) \<partial>count_space (set_spmf x)"
      by(simp add: ennreal_spmf_bind ennreal_spmf_lub_spmf[OF chain'] Y nn_integral_measure_spmf' SUP_mult_left_ennreal ennreal_mult image_comp)
    also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ y. ennreal (spmf x y * spmf (g y p) i) \<partial>count_space (set_spmf x))"
      unfolding nn_integral_measure_spmf' using Y chain''
      by(rule nn_integral_monotone_convergence_SUP_countable) simp
    also have "\<dots> = (SUP p\<in>Y. ennreal (spmf (bind_spmf x (\<lambda>y. g y p)) i))"
      by(simp add: ennreal_spmf_bind nn_integral_measure_spmf' ennreal_mult)
    also have "\<dots> = ennreal (spmf ?rhs i)" using chain'''
      by(auto simp add: ennreal_spmf_lub_spmf Y image_comp)
    finally show "spmf ?lhs i = spmf ?rhs i" by simp
  qed
qed simp
*)

lemma mcont_bind_pmfs [cont_intro]:
  assumes f: "mcont luba orda lub_pmfs ord_pmfs f"
  and g: "\<And>y. mcont luba orda lub_pmfs ord_pmfs (g y)"
  shows "mcont luba orda lub_pmfs ord_pmfs (\<lambda>x. bind_pmfs (f x) (\<lambda>y. g y x))"
proof(rule pmfs.mcont2mcont'[OF _ _ f])
  fix z
  show "mcont lub_pmfs ord_pmfs lub_pmfs ord_pmfs (\<lambda>x. bind_pmfs x (\<lambda>y. g y z))"
    by(rule mcont_bind_pmfs1)
next
  fix x
  let ?f = "\<lambda>z. bind_pmfs x (\<lambda>y. g y z)"
  have "monotone orda ord_pmfs ?f" using mcont_mono[OF g] by(rule monotone_bind_pmfs2)
  moreover have "cont luba orda lub_pmfs ord_pmfs ?f"
  proof(rule contI)
    fix Y
    assume chain: "Complete_Partial_Order.chain orda Y" and Y: "Y \<noteq> {}"
    have "bind_pmfs x (\<lambda>y. g y (luba Y)) = bind_pmfs x (\<lambda>y. lub_pmfs (g y ` Y))"
      by (rule bind_pmfs_cong) (simp_all add: mcont_contD[OF g chain Y])
    also have "\<dots> = lub_pmfs ((\<lambda>p. bind_pmfs x (\<lambda>y. g y p)) ` Y)" using chain
      by (rule bind_lub_pmfs2)(rule mcont_mono[OF g])
    finally show "bind_pmfs x (\<lambda>y. g y (luba Y)) = \<dots>" .
  qed
  ultimately show "mcont luba orda lub_pmfs ord_pmfs ?f" by(rule mcontI)
qed

lemma map_pmfs_mono [partial_function_mono]: "mono_pmfs B \<Longrightarrow> mono_pmfs (\<lambda>g. map_pmfs f (B g))"
  unfolding map_pmfs_conv_bind_pmfs by(rule bind_pmfs_mono) simp_all

lemma mcont_map_pmfs [cont_intro]:
  "mcont luba orda lub_pmfs ord_pmfs g
  \<Longrightarrow> mcont luba orda lub_pmfs ord_pmfs (\<lambda>x. map_pmfs f (g x))"
  unfolding map_pmfs_conv_bind_pmfs by (rule mcont_bind_pmfs) simp_all

lemma replicate_pmfs_mono [partial_function_mono]:
  "mono_pmfs B \<Longrightarrow> mono_pmfs (\<lambda>g. replicate_pmfs n (B g))"
  by (induction n) (auto intro!: partial_function_mono)

lemma mcont_replicate_pmfs [cont_intro]:
  assumes f: "mcont luba orda lub_pmfs ord_pmfs f"
  shows "mcont luba orda lub_pmfs ord_pmfs (\<lambda>x. replicate_pmfs n (f x))"
  by (induction n) (auto intro!: cont_intro assms)



lemma monotone_set_pmfs: "monotone ord_pmfs (\<subseteq>) range_pmfs"
  unfolding monotone_def
  by transfer (use monotone_set_pmfsr in \<open>auto simp: monotone_def\<close>)

lemma cont_set_pmfs: "cont lub_pmfs ord_pmfs Union (\<subseteq>) range_pmfs"
  oops

lemma mcont2mcont_set_pmfs[THEN mcont2mcont, cont_intro]:
  shows mcont_set_pmfs: "mcont lub_pmfs ord_pmfs Union (\<subseteq>) range_pmfs"
  oops
(*
by(rule mcontI monotone_set_pmfs cont_set_pmfs)+
*)



definition random_bit_list
  where "random_bit_list = [False, False, True, True, True, False, True, True, False, False, False, False, True,
 True, True, False, False, True, True, True, True, True, True, True, False, False, True,
 True, False, True, False, True, False, False, False, False, True, True, True, True,
 True, False, True, False, False, True, False, True, True, False, False, False, True,
 False, True, True, False, True, False, False, False, False, True, True, True, False,
 False, False, False, True, True, True, True, False, False, False, True, True, False,
 True, False, True, False, False, True, False, True, False, False, True, False, True,
 True, False, False, False, False, False, False, False, False, True, True, False, True,
 False, True, False, True, False, True, False, True, True, False, True, True, True,
 True, True, True, False, True, True, False, True, True, True, False, True, True, False,
 False, False, True, True, True, True, True, False, True, False, False, False, False,
 False, False, False, False, False, False, False, True, False, False, False, False,
 True, False, False, False, True, True, False, False, False, True, False, False, True,
 True, True, True, False, True, False, False, False, True, True, False, False, False,
 True, False, False, False, True, True, False, True, False, False, False, True, False,
 True, True, False, True, True, True, True, False, False, True, True, False, True,
 False, False, True, False, False, False, False, False, False, True, True, True, False,
 True, False, False, False, False, False, False, False, False, True, True, True, True,
 False, True, True, True, False, False, True, False, True, False, True, False, False,
 True, True, False, True, True, True, True, True, False, False, True, True, True, False,
 False, True, False, False, False, False, False, False, True, False, True, True, False,
 True, True, False, False, False, False, True, False, False, False, True, False, True,
 True, False, True, False, False, True, True, True, False, True, True, False, False,
 True, False, False, True, True, True, True, False, False, True, False, False, False,
 False, False, True, True, False, False, True, True, False, True, True, True, False,
 True, True, True, True, True, True, True, True, True, True, True, False, True, False,
 True, False, True, True, True, True, True, True, False, False, True, False, True,
 False, False, True, False, True, False, False, False, False, False, False, True, False,
 True, False, True, True, False, False, True, True, False, True, True, False, True,
 False, True, False, True, True, False, True, True, True, True, True, False, True,
 False, False, False, False, True, False, True, False, True, True, False, True, False,
 False, False, True, True, False, False, False, True, False, False, False, False, False,
 False, True, False, True, True, False, False, True, False, True, True, False, False,
 False, False, False, False, True, False, True, False, True, True, False, True, False,
 True, True, True, False, True, True, False, True, True, True, False, True, False,
 False, True, True, True, False, True, True, True, True, True, True, False, True, False,
 True, False, False, True, False, True, True, False, False, False, False, True, False,
 False, True, True, False, True, True, True, False, True, False, True, False, False,
 False, True, True, True, True, True, False, True, True, False, False, True, True, True,
 False, False, True, True, False, True, True, False, False, False, False, False, True,
 True, True, False, False, False, True, True, False, True, True, True, False, True,
 False, True, True, True, False, False, True, True, False, True, False, True, False,
 False, False, True, True, True, False, False, True, True, False, True, True, False,
 False, False, True, False, False, False, False, True, False, False, True, True, False,
 True, True, False, True, False, False, True, True, True, False, True, True, True, True,
 False, False, True, True, True, False, False, False, True, False, True, False, False,
 True, True, False, True, False, False, True, False, False, True, True, True, False,
 True, True, True, False, True, False, True, True, False, True, False, False, True,
 False, False, True, False, True, False, False, True, True, True, True, True, True,
 False, False, False, False, True, True, True, False, True, True, True, False, True,
 False, False, True, True, True, True, True, False, False, False, True, True, False,
 True, False, True, True, True, False, False, True, True, False, True, False, True,
 True, True, False, False, True, True, True, True, False, False, True, False, False,
 False, True, True, True, False, True, False, True, False, True, True, False, False,
 False, False, False, False, False, True, False, False, True, True, True, True, True,
 True, False, True, True, True, False, True, False, False, False, False, True, True,
 True, True, True, True, True, True, True, True, True, True, True, True, False, False,
 True, False, True, True, False, True, False, True, False, False, True, False, False,
 True, True, False, False, False, True, False, False, True, False, False, True, True,
 True, True, False, False, True, False, True, True, True, True, True, True, False,
 False, False, False, False, False, False, False, True, True, False, True, False, True,
 True, True, True, True, True, False, True, True, True, False, False, True, True, False,
 False, False, False, True, True, False, True, True, True, True, True, True, True, True,
 False, True, False, True, True, True, True, False, True, False, True, True, True, True,
 True, True, False, True, True, False, True, False, True, False, True, True, False,
 True, True, True, False, False, False, True, False, True, True, False, False, False,
 True, False, True, True, False, True, True, False, False, True, False, True, False,
 False, False, False, True, False, False, False, True, True, False, True, False, False,
 False, True, True, True, True, True, False, False, False, False, True, False, False,
 True, False, False, True, True, True, True, False, True, True, False, True, False,
 True, True, True, True, False, False, False, False, False, True, True, True, True,
 True, False, True, True, False, False, True, True, False, False, True, False, True,
 True, False, False, True, False, True, True, False, True, True, True, True, False,
 False, False, False, True, True, True, True, True, True, True, False, True, True, True,
 True, False, False, True, True, True, False, True, True, True, True, False, True,
 False, False, False, True, False, True, True, True, True, False, False, False, True,
 False]"


definition random_bits
  where "random_bits i = cycle (rotate i random_bit_list)"


code_lazy_type stream

partial_function (pmfs) bernoulli_pmfs :: "real \<Rightarrow> bool pmfs" where
  "bernoulli_pmfs p =
     do {b \<leftarrow> coin_pmfs;
         if b then
           return_pmfs (p \<ge> 1/2)
         else
           bernoulli_pmfs (if p < 1/2 then 2 * p else 2 * p - 1)}"

lemmas [code] = bernoulli_pmfs.simps

value "run_pmfs' (bernoulli_pmfs (1/3)) (random_bits 1)"
value "run_pmfs' (bernoulli_pmfs (1/3)) (random_bits 2)"
value "run_pmfs' (bernoulli_pmfs (1/3)) (random_bits 8)"


partial_function (pmfs) geometric_pmfs :: "real \<Rightarrow> nat pmfs" where
  "geometric_pmfs p =
     do {b \<leftarrow> bernoulli_pmfs p;
         if b then return_pmfs 0 else map_pmfs Suc (geometric_pmfs p)}"

lemmas [code] = geometric_pmfs.simps


value "run_pmfs' (geometric_pmfs (1/3)) (random_bits 1)"
value "map (\<lambda>i. fst (the (run_pmfs' (geometric_pmfs (1/3)) (random_bits i)))) [0..<100]"


lemma loss_pmfs_bernoulli [simp]: "loss_pmfs (bernoulli_pmfs p) = 0"
proof -
  define f where "f = (\<lambda>p. loss_pmfs (bernoulli_pmfs p))"
  have f_rec: "f p = f (if p < 1 / 2 then 2 * p else 2 * p - 1) / 2" for p
    unfolding f_def
    by (subst bernoulli_pmfs.simps)
       (simp_all add: loss_bind_pmfs spmf_of_set_def integral_pmf_of_set UNIV_bool
                 del: spmf_of_pmf_pmf_of_set)
  have f_01: "f p \<in> {0..1}" for p
    using loss_pmfs_01[of "bernoulli_pmfs p"] by (auto simp: f_def)
  have f_le: "f p \<le> 1 / 2 ^ n" for n
  proof (induction n arbitrary: p)
    case (Suc p)
    thus ?case
      using f_01[of p] by (auto simp: f_rec[of p])
  qed (use f_01 in auto)
  show "f p = 0"
  proof (rule ccontr)
    assume "f p \<noteq> 0"
    with f_01[of p] have "f p > 0"
      by auto
    have "\<exists>n. 2 ^ n > 1 / f p"
      by (rule real_arch_pow) auto
    then obtain n where "2 ^ n > 1 / f p"
      by auto
    hence "f p > 1 / 2 ^ n"
      using \<open>f p > 0\<close> by (auto simp: field_simps)
    with f_le[of n] show False
      by simp
  qed
qed

lemma spmf_of_pmfs_bernoulli [simp]: "spmf_of_pmfs (bernoulli_pmfs p) = spmf_of_pmf (bernoulli_pmf p)"
  sorry


lemma loss_pmfs_geometric [simp]:
  assumes "p \<in> {0<..1}"
  shows   "loss_pmfs (geometric_pmfs p) = 0"
proof -
  have "loss_pmfs (geometric_pmfs p) = loss_pmfs (geometric_pmfs p) * (1 - p)"
    using assms by (subst geometric_pmfs.simps) (simp_all add: loss_bind_pmfs)
  thus "loss_pmfs (geometric_pmfs p) = 0"
    using assms by (auto simp: algebra_simps)
qed



partial_function (pmfs) while_pmfs :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a pmfs) \<Rightarrow> 'a \<Rightarrow> 'a pmfs" where
  "while_pmfs guard body s =
     (if guard s then return_pmfs s else body s \<bind> while_pmfs guard body)"

lemmas [code] = while_pmfs.simps

value "run_pmfs (while_pmfs (\<lambda>n::nat. n > 42) (\<lambda>n. map_pmfs (\<lambda>b. of_bool b + 2 * n) coin_pmfs) 0) (random_bits 0)"
value "run_pmfs (while_pmfs (\<lambda>n::nat. n > 42) (\<lambda>n. map_pmfs (\<lambda>b. of_bool b + 2 * n) coin_pmfs) 0) (random_bits 4)"
value "run_pmfs (while_pmfs (\<lambda>n::nat. n > 42) (\<lambda>n. map_pmfs (\<lambda>b. of_bool b + 2 * n) coin_pmfs) 0) (random_bits 5)"



datatype 'a mytree = Node 'a "'a mytree list"

partial_function (pmfs) foo :: "real \<Rightarrow> bool mytree pmfs" where
  "foo p = do {
     b \<leftarrow> coin_pmfs;
     n \<leftarrow> geometric_pmfs p; map_pmfs (\<lambda>xs. Node b xs) (replicate_pmfs n (foo (2 * p)))}"

lemmas [code] = foo.simps

value "run_pmfs' (foo 0.1) (random_bits 1)"
value "run_pmfs' (foo 0.1) (random_bits 2)"
value "run_pmfs' (foo 0.1) (random_bits 3)"


context
  fixes n :: nat
begin

partial_function (pmfs) fast_dice_roll :: "nat \<Rightarrow> nat \<Rightarrow> nat pmfs"
where
  "fast_dice_roll v c = 
  (if v \<ge> n then if c < n then return_pmfs c else fast_dice_roll (v - n) (c - n)
   else do {
     b \<leftarrow> coin_pmfs;
     fast_dice_roll (2 * v) (2 * c + (if b then 1 else 0)) } )"

definition fast_uniform :: "nat pmfs"
  where "fast_uniform = fast_dice_roll 1 0"

end

lemmas [code] = fast_dice_roll.simps

value "run_pmfs' (fast_uniform 10) ([True, False, True, True, False] @- sconst False)"
value "run_pmfs' (fast_uniform 10) ([False, False, True, True, False] @- sconst False)"
value "run_pmfs' (fast_uniform 10) ([True, False, True, False, False] @- sconst False)"
value "run_pmfs' (fast_uniform 10) ([True, False, True, True, True] @- sconst False)"
value "run_pmfs' (fast_uniform 10) ([True, False, True, True, False, True, True, False, True] @- sconst False)"
value "run_pmfs' (fast_uniform 10) ([True, True, True, True, True, True, False, True, True] @- sconst False)"
value "map (\<lambda>i. fst (the (run_pmfs' (fast_uniform 10) (random_bits i)))) [0..<100]"
value "run_pmfs' (replicate_pmfs 100 (fast_uniform 10)) (random_bits 0)"
value "run_pmfs' (replicate_pmfs 100 (fast_uniform 10)) (random_bits 43)"
value "run_pmfs (consumption_pmfs (replicate_pmfs 100 (fast_uniform 10))) (random_bits 43)"


ML_val \<open>
@{theory}
|> Theory.defs_of
|> (fn defs => Defs.specifications_of defs (Defs.Const, @{const_name bernoulli_pmfs}))
|> map (#def #> the)
\<close>

ML_val \<open>
@{theory}
|> Global_Theory.facts_of
|> (fn f => Facts.extern @{context} f "PMF_Sampler.bernoulli_pmfs_def")
\<close>

ML_val \<open>
@{theory}
|> Theory.axiom_table
|> (fn tbl => Name_Space.lookup tbl "PMF_Sampler.bernoulli_pmfs_def")
|> the
|> Syntax.pretty_term @{context}
|> Pretty.writeln
\<close>

term "ccpo.fixp (fun_lub lub_pmfs) (fun_ord ord_pmfs)"

thm ccpo.fixp_def[OF pmfs.ccpo]
thm ccpo.iterates_def[OF pmfs.ccpo]

find_theorems ccpo.fixp monotone "_ = _" name:Complete "ccpo.fixp"

thm fun_lub_def

ML_val \<open>@{term "pmfs.fixp_fun"}\<close>


end