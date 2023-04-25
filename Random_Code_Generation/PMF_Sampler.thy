theory PMF_Sampler
  imports "HOL-Probability.Probability" "HOL-Library.Code_Lazy" Prereqs Prefix_Tree
begin

(* TODO Move *)
lemma sprefix_append: "sprefix (xs @ ys) zs \<longleftrightarrow> sprefix xs zs \<and> sprefix ys (sdrop (length xs) zs)"
  by (auto simp add: sprefix_altdef)


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

lemma prob_coin_space_stake:
  assumes "\<And>xs. xs \<in> A \<Longrightarrow> length xs = n"
  shows   "coin_space.prob (stake n -` A) = card A / 2 ^ n"
  using emeasure_coin_space_stake[OF assms, of A] by (simp add: coin_space.emeasure_eq_measure)

lemma emeasure_coin_space_shd: "emeasure coin_space (shd -` A) = card A / 2"
proof -
  have "shd -` A = stake 1 -` (\<lambda>b. [b]) ` A"
    by safe simp_all
  also have "emeasure coin_space \<dots> = ennreal (real (card ((\<lambda>b. [b]) ` A)) / 2)"
    by (subst emeasure_coin_space_stake) auto
  also have "\<dots> = ennreal (real (card A) / 2)"
    by (subst card_image) (auto simp: inj_on_def)
  finally show ?thesis .
qed

lemma prob_coin_space_shd: "coin_space.prob (shd -` A) = card A / 2"
  using emeasure_coin_space_shd[of A] by (simp add: coin_space.emeasure_eq_measure)



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

lemma sampler_eq_iff: "p = q \<longleftrightarrow> (\<forall>bs. run_sampler p bs = run_sampler q bs)"
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

lemma bind_return_sampler [simp]: "return_sampler x \<bind> f = f x"
  by transfer auto

lemma bind_return_sampler' [simp]: "p \<bind> return_sampler = p"
  by transfer auto

lemma map_conv_bind_sampler: "map_sampler f p = bind_sampler p (\<lambda>x. return_sampler (f x))"
  by transfer (auto simp: Option_bind_conv_case split: option.splits)

lemma map_return_sampler [simp]: "map_sampler f (return_sampler x) = return_sampler (f x)"
  by transfer auto

lemma map_map_sampler: "map_sampler f (map_sampler g p) = map_sampler (f \<circ> g) p"
  by transfer (auto simp: option.map_comp o_def prod.map_comp id_def)
 
lemma bind_sampler_decompose:
  "map_sampler f (sampler_of_ptree t1) \<bind> (\<lambda>x. map_sampler (g x) (sampler_of_ptree (t2 x))) =
   map_sampler (\<lambda>(bs,bs'). g (f bs) bs')
     (do {bs \<leftarrow> sampler_of_ptree t1; bs' \<leftarrow> sampler_of_ptree (t2 (f bs)); return_sampler (bs, bs')})"
  by (simp add: map_bind_sampler bind_assoc_sampler bind_map_sampler o_def map_map_sampler
           flip: map_conv_bind_sampler)

lemma ord_option_case:
  "ord_option le x y \<longleftrightarrow>
     (case x of None \<Rightarrow> True | Some x' \<Rightarrow> (case y of None \<Rightarrow> False | Some y' \<Rightarrow> le x' y'))"
  by (auto split: option.splits)


primrec list_sampler :: "'a sampler list \<Rightarrow> 'a list sampler" where
  "list_sampler [] = return_sampler []"
| "list_sampler (p # ps) = do {x \<leftarrow> p; map_sampler ((#) x) (list_sampler ps)}"

lemma list_sampler_append:
  "list_sampler (ps @ qs) =
     do {xs \<leftarrow> list_sampler ps; ys \<leftarrow> list_sampler qs; return_sampler (xs @ ys)}"
  by (induction ps) (auto simp: bind_assoc_sampler map_conv_bind_sampler)

lemma list_sampler_map:
  "list_sampler (map (map_sampler f) ps) = map_sampler (map f) (list_sampler ps)"
  by (induction ps) (auto simp: bind_assoc_sampler map_conv_bind_sampler)


primrec replicate_sampler :: "nat \<Rightarrow> 'a sampler \<Rightarrow> 'a list sampler" where
  "replicate_sampler 0 p = return_sampler []"
| "replicate_sampler (Suc n) p = do {x \<leftarrow> p; map_sampler ((#) x) (replicate_sampler n p)}"

lemma replicate_sampler_return [simp]:
  "replicate_sampler n (return_sampler x) = return_sampler (replicate n x)"
  by (induction n) auto

lemma replicate_sampler_add:
  "replicate_sampler (m + n) p = 
     do {xs \<leftarrow> replicate_sampler m p; ys \<leftarrow> replicate_sampler n p; return_sampler (xs @ ys)}"
  by (induction m) (auto simp: bind_assoc_sampler map_conv_bind_sampler)

lemma map_replicate_sampler [simp]:
  "replicate_sampler n (map_sampler f p) = map_sampler (map f) (replicate_sampler n p)"
  by (induction n) (auto simp: map_conv_bind_sampler bind_assoc_sampler)

lemma list_sampler_replicate [simp]:
  "list_sampler (replicate n p) = replicate_sampler n p"
  by (induction n) auto
   



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

lemma le_imp_fun_sampler_eq:
  assumes "p \<le> q" "bs \<in> set_ptree (ptree_of_sampler p)"
  shows   "fun_sampler p bs = fun_sampler q bs"
  using assms unfolding fun_sampler_altdef set_ptree_of_sampler using le_samplerD1 by fastforce




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

lemma map_sampler_cong [cong]:
  "(\<And>x. x \<in> range_sampler p \<Longrightarrow> f x = g x) \<Longrightarrow> p = p' \<Longrightarrow> map_sampler f p = map_sampler g p'"
  by (rule sampler_eqI)
     (auto simp: map_option_case in_range_samplerI split: option.splits)

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

lemma map_option_mono':
  "ord_option rel x y \<Longrightarrow> monotone rel rel' f \<Longrightarrow>
   ord_option rel' (map_option f x) (map_option f y)"
  by (auto simp: ord_option_case monotone_def split: option.splits)

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

lemma run_sampler_mono':
  "p \<le> q \<Longrightarrow> bs = bs' \<Longrightarrow> ord_option (=) (run_sampler p bs) (run_sampler q bs')"
  using run_sampler_mono[of p q] unfolding ord_pmfsr_def rel_fun_def by blast

lemma bind_option_mono:
  assumes "ord_option le x y" "\<And>x' y'. x = Some x' \<Longrightarrow> y = Some y' \<Longrightarrow> ord_option le' (f x') (g y')"
  shows   "ord_option le' (Option.bind x f) (Option.bind y g)"
  using assms by (auto simp: Option_bind_conv_case split: option.splits)

lemma le_samplerI: "(\<And>bs. ord_option (=) (run_sampler p bs) (run_sampler q bs)) \<Longrightarrow> p \<le> q"
  by (simp add: less_eq_sampler_altdef)

lemma le_samplerD1':
   "p \<le> q \<Longrightarrow> run_sampler p bs = Some xn \<Longrightarrow> run_sampler q bs = Some xn' \<Longrightarrow> xn = xn'"
  using le_samplerD1[of p q bs xn] by simp

lemma
  assumes "p \<le> q" "run_sampler p bs = Some (x, n)" "run_sampler q bs = Some (y, m)"
  shows   le_samplerD1_fst: "x = y" and le_samplerD1_snd: "n = m"
  using le_samplerD1[of p q bs] assms by simp_all

lemma bind_sampler_mono_strong:
  assumes "p \<le> p'" "\<And>x. x \<in> range_sampler p \<Longrightarrow> q x \<le> q' x"
  shows   "bind_sampler p q \<le> bind_sampler p' q'"
proof -
  have q: "q x \<le> q' y" if "x \<in> range_sampler p" "x = y" for x y
    using assms that by blast
  have q': "z1 = z2" "n = m"
    if "run_sampler (q x) bs = Some (z1, n)" "run_sampler (q' y) bs' = Some (z2, m)"
       "x \<in> range_sampler p" "x = y" "bs = bs'" for x y bs bs' z1 z2 n m
    using that le_samplerD1'[OF q that(1,2)[unfolded \<open>bs = bs'\<close>]] by simp_all
  show ?thesis
  proof (rule le_samplerI)
    fix bs :: "bool stream"
    show "ord_option (=) (run_sampler (p \<bind> q) bs) (run_sampler (p' \<bind> q') bs)"
      unfolding run_sampler_bind
      by (rule bind_option_mono run_sampler_mono' assms q ord_option.intros
               arg_cong[of _ _ "\<lambda>n. sdrop n bs" for bs] arg_cong2[of _ _ _ _ "(+)"]
             | erule in_range_samplerI
             | erule (1) le_samplerD1_fst[OF assms(1)] le_samplerD1_snd[OF assms(1)] q'
             | safe)+
  qed
qed

lemma bind_sampler_mono:
  "p \<le> p' \<Longrightarrow> (\<And>x. q x \<le> q' x) \<Longrightarrow> bind_sampler p q \<le> bind_sampler p' q'"
  by (rule bind_sampler_mono_strong)

lemma bind_sampler_cong [cong]:
  "p = p' \<Longrightarrow> (\<And>x. x \<in> range_sampler p \<Longrightarrow> q x = q' x) \<Longrightarrow> bind_sampler p q = bind_sampler p' q'"
  by (intro antisym bind_sampler_mono_strong) auto

lemma range_sampler_empty_iff: "range_sampler p = {} \<longleftrightarrow> p = bot"
proof
  assume "range_sampler p = {}"
  hence "run_sampler p bs = None" for bs
    using in_range_samplerI[of p bs] by (cases "run_sampler p bs") auto
  thus "p = bot"
    by (auto simp: sampler_eq_iff)
qed auto

lemma map_sampler_eq_bot_iff [simp]: "map_sampler f p = bot \<longleftrightarrow> p = bot"
  by (auto simp flip: range_sampler_empty_iff)

lemma ptree_of_sampler_bot [simp]: "ptree_of_sampler bot = bot"
  by (metis map_sampler_eq_bot_iff range_sampler_bot range_sampler_of_ptree 
            sampler_decompose set_ptree_bot set_ptree_inverse)



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

lemma vimage_mono': "(\<And>x. f x \<in> A \<Longrightarrow> g x \<in> B) \<Longrightarrow> f -` A \<subseteq> g -` B"
  by blast

lemma compatible_sampler_sampler_of_ptree:
  "ptree_compatible X \<Longrightarrow> compatible_sampler (sampler_of_ptree ` X)"
  by (metis (mono_tags, opaque_lifting) Sup_ptree_upper compatible_sampler_def imageE sampler_of_ptree_le_iff)

lemma ptree_compatible_ptree_of_sampler:
  "compatible_sampler X \<Longrightarrow> ptree_compatible (ptree_of_sampler ` X)"
  unfolding compatible_sampler_def ptree_compatible_def
  apply (auto simp: pairwise_def pairwise'_def)
  by (meson in_mono less_eq_ptree.rep_eq ptree_of_sampler_mono set_ptreeD)

lemma Sup_sampler_of_ptree:
  assumes "ptree_compatible X"
  shows   "Sup (sampler_of_ptree ` X) = sampler_of_ptree (Sup X)"
  apply (rule antisym)
  using assms
   apply (smt (verit, ccfv_SIG) Sup_ptree_upper Sup_sampler_least imageE sampler_of_ptree_mono)
  apply (rule le_samplerI)
  using assms compatible_sampler_sampler_of_ptree[OF assms]
  apply (auto simp: run_sampler_of_ptree ord_option_case run_sampler_Sup_simps prefix_of_ptree_simps set_ptree_Sup
              split: option.splits)
   apply (metis Prefix_Tree.ptree_compatible_altdef in_mono less_eq_ptree.rep_eq parallel_def set_ptree_prefixD sprefix_altdef sprefix_shiftD)
  apply (metis Prefix_Tree.ptree_compatible_altdef in_mono less_eq_ptree.rep_eq parallel_def set_ptree_prefixD sprefix_altdef sprefix_shiftD)
  done

lemma Sup_ptree_of_sampler:
  assumes "compatible_sampler X"
  shows   "Sup (ptree_of_sampler ` X) = ptree_of_sampler (Sup X)"
  apply (rule antisym)
  subgoal
   apply (rule Sup_ptree_least)
    apply (auto intro!: ptree_of_sampler_mono Sup_sampler_upper assms)
    done
  unfolding less_eq_ptree_def using assms ptree_compatible_ptree_of_sampler[OF assms]
  apply (auto simp: set_ptree_of_sampler set_ptree_Sup run_sampler_Sup_simps)
  done

lemma compatible_sampler_sampler_of_ptree_iff [simp]:
  "compatible_sampler (sampler_of_ptree ` X) \<longleftrightarrow> ptree_compatible X"
  apply auto
   apply (metis image_eqI ptree_compatible_altdef ptree_compatible_ptree_of_sampler ptree_of_sampler_of_ptree)
  apply (erule compatible_sampler_sampler_of_ptree)
  done

lemma compatible_sampler_image:
  assumes "compatible_sampler Y" "mono f"
  shows   "compatible_sampler (f ` Y)"
  using assms by (auto simp: compatible_sampler_def mono_def)

lemma ptree_of_sampler_eqI: "map_sampler f (sampler_of_ptree t) = p \<Longrightarrow> ptree_of_sampler p = t"
  by fastforce
  

lemma ptree_of_sampler_bind_aux:
  "ptree_of_sampler (do {bs \<leftarrow> sampler_of_ptree p; bs' \<leftarrow> sampler_of_ptree (q bs); return_sampler (bs, bs')}) =
   bind_ptree p q"
proof -
  define f where "f = (\<lambda>bs. let xs = the (prefix_of_ptree p (bs @- sconst False)) in (xs, drop (length xs) bs))"
  show ?thesis
    apply (rule ptree_of_sampler_eqI[where f = f])
    apply (rule sampler_eqI)
    apply (auto simp: run_sampler_of_ptree run_sampler_bind Option_bind_conv_case)
    apply (auto split: option.splits)
      apply (auto simp: prefix_of_ptree_simps set_ptree_bind sprefix_append)
     apply (metis option.sel prefix_of_ptree_eq_Some_iff)
    apply (auto simp: sprefix_altdef)
    apply (auto simp: f_def Let_def)
    subgoal for bs1 bs2
      apply (rule exI[of _ "bs1 @ bs2"])
      apply (auto simp: prefix_of_ptree_eq_SomeI)
      done
    done
qed

lemma ptree_eqI: "set_ptree t = set_ptree t' \<Longrightarrow> t = t'"
  by transfer auto

lemma bind_ptree_cong [cong]:
  "t = t' \<Longrightarrow> (\<And>x. x \<in> set_ptree t \<Longrightarrow> f x = f' x) \<Longrightarrow> bind_ptree t f = bind_ptree t' f'"
  by (rule ptree_eqI) (auto simp: set_ptree_bind)
  

lemma sampler_fun_cases [cases type]:
  obtains f t where "p = (\<lambda>x. map_sampler (f x) (sampler_of_ptree (t x)))"
  using sampler_decompose[of "p x" for x] that by fast

lemma ptree_of_sampler_bind:
  "ptree_of_sampler (sampler_of_ptree t \<bind> q) = bind_ptree t (ptree_of_sampler \<circ> q)"
proof (cases q)
  case [simp]: (1 fq tq)
  show ?thesis
    using bind_sampler_decompose[of id t fq tq]
    by (auto simp add: ptree_of_sampler_bind_aux o_def fun_sampler_map
             intro: bind_ptree_cong)
qed

lemma sampler_decompose_set:
  assumes "compatible_sampler Y" "p \<in> Y"
  shows   "p = map_sampler (fun_sampler (Sup Y)) (sampler_of_ptree (ptree_of_sampler p))"
  apply (subst sampler_decompose[of p])
  apply (rule map_sampler_cong)
   apply (auto)
  apply (simp add: Sup_sampler_upper assms(1) assms(2) le_imp_fun_sampler_eq)
  done

lemma sampler_set_cases [cases type]:
  assumes "compatible_sampler Y"
  obtains Y' f where "Y = map_sampler f ` sampler_of_ptree ` Y'" "ptree_compatible Y'"
                     "Sup Y = map_sampler f (sampler_of_ptree (Sup Y'))"
                      
proof -
  define f where "f = fun_sampler (Sup Y)"
  define Y' where "Y' = ptree_of_sampler ` Y"
  show ?thesis
  proof (rule that[of f Y'])
    have "id ` Y = map_sampler f ` sampler_of_ptree ` Y'"
      unfolding image_image Y'_def f_def using assms
      apply (intro image_cong refl)
      apply (auto )
      using sampler_decompose_set by blast
    thus Y: "Y = map_sampler f ` sampler_of_ptree ` Y'"
      by simp
    show comp: "ptree_compatible Y'"
      unfolding Y'_def using assms by (rule ptree_compatible_ptree_of_sampler)
    show "\<Squnion> Y = map_sampler f (sampler_of_ptree (\<Squnion> Y'))"
      using comp Y by (simp add: Sup_map_sampler Sup_sampler_of_ptree)
  qed
qed

lemma bind_singleton_ptree_Nil [simp]: "bind_ptree t (\<lambda>x. singleton_ptree []) = t"
  by (rule ptree_eqI, subst set_ptree_bind) auto

lemma ptree_compatible_image: "ptree_compatible Y \<Longrightarrow> mono f \<Longrightarrow> ptree_compatible (f ` Y)"
  unfolding ptree_compatible_altdef by (auto simp: mono_def)

lemma Sup_bind_ptree1:
  assumes "ptree_compatible Y"
  shows   "bind_ptree (Sup Y) t' = Sup ((\<lambda>t. bind_ptree t t') ` Y)"
  apply (rule ptree_eqI)
  apply (subst set_ptree_bind)
  using assms
  apply (subst (1 2) set_ptree_Sup)
    apply (auto intro!: ptree_compatible_image monoI bind_ptree_mono)
   apply (auto simp: set_ptree_bind)
  done


lemma sampler_eqI_via_ptree:
  assumes "ptree_of_sampler p = ptree_of_sampler q" "p \<le> q"
  shows   "p = q"
  using assms
  apply (cases p; cases q)
  apply auto
  by (metis le_imp_fun_sampler_eq map_sampler_cong ptree_of_sampler_eqI range_sampler_of_ptree sampler_decompose)

lemma Sup_bind_sampler1:
  assumes comp: "compatible_sampler Y"
  shows   "bind_sampler (Sup Y) q = Sup ((\<lambda>p. bind_sampler p q) ` Y)" (is "?lhs = ?rhs")
proof (rule sym, rule sampler_eqI_via_ptree)
  obtain Y' f_Y' where Y':
    "Y = map_sampler f_Y' ` sampler_of_ptree ` Y'" "ptree_compatible Y'"
    "\<Squnion> Y = map_sampler f_Y' (sampler_of_ptree (\<Squnion> Y'))"
    using comp by (cases Y)
  obtain g t where q: "q = (\<lambda>x. map_sampler (g x) (sampler_of_ptree (t x)))"
    by (cases q)

  note [simp] = Y'(1,3) q

  have "Sup ((\<lambda>p. bind_sampler p q) ` Y) =
          (\<Squnion>x\<in>map_sampler f_Y' ` sampler_of_ptree ` Y'.
              x \<bind> (\<lambda>x. map_sampler (g x) (sampler_of_ptree (t x))))"
    using Y'(2) by (simp add: Sup_map_sampler Sup_sampler_of_ptree bind_map_sampler)

  show "bind_sampler (Sup Y) q \<ge> Sup ((\<lambda>p. bind_sampler p q) ` Y)"
    using Y'(2)
    apply (intro Sup_sampler_least)
    apply (auto intro!: bind_sampler_mono Sup_sampler_upper compatible_sampler_image monoI map_sampler_mono)
    done

  show "ptree_of_sampler ?rhs = ptree_of_sampler ?lhs"
    using Y'(2)
    apply (simp add: Sup_map_sampler Sup_sampler_of_ptree bind_map_sampler
                     ptree_of_sampler_bind Sup_ptree_of_sampler)
    apply (subst Sup_ptree_of_sampler [symmetric])
     apply (intro compatible_sampler_image compatible_sampler_sampler_of_ptree monoI Y'
                  map_sampler_mono bind_sampler_mono sampler_of_ptree_mono order.refl | assumption)+
    apply (simp add: image_image)
    apply (simp add: bind_sampler_decompose)
    apply (simp add: ptree_of_sampler_bind Sup_bind_ptree1)
    done  
qed

lemma Sup_bind_ptree2:
  assumes chain: "Complete_Partial_Order.chain le Y"
  assumes mono: "\<And>x. monotone le (\<le>) (q x)"
  shows "\<Squnion> (bind_ptree t ` (\<lambda>x y. q y x) ` Y) = bind_ptree t (\<lambda>y. \<Squnion> (q y ` Y))"
  unfolding image_image
  apply (rule ptree_eqI)
  apply (subst set_ptree_Sup)
   apply (intro ptree_chain_imp_compatible chain_imageI[OF chain] bind_ptree_mono order.refl
                monotoneD[OF mono])
   apply simp
  apply (subst set_ptree_bind)
  apply (subst set_ptree_Sup)
   apply (intro ptree_chain_imp_compatible chain_imageI[OF chain] bind_ptree_mono order.refl
                monotoneD[OF mono])
   apply (auto simp: set_ptree_bind set_ptree_Sup)
done


lemma Sup_bind_sampler2:
  fixes p :: "'a sampler" and q :: "'a \<Rightarrow> 'b \<Rightarrow> 'c sampler"
  assumes chain: "Complete_Partial_Order.chain le Y"
  assumes mono:  "\<And>x. monotone le (\<le>) (q x)"
  shows   "p \<bind> (\<lambda>x. Sup (q x ` Y)) = Sup ((\<lambda>y. p \<bind> (\<lambda>x. q x y)) ` Y)"
proof (rule sym, rule sampler_eqI_via_ptree)
  obtain fp tp where p_eq: "p = map_sampler fp (sampler_of_ptree tp)"
    by (cases p)
  have comp: "compatible_sampler (q x ` Y)" for x
    by (intro chain_imp_compatible_sampler chain_imageI[OF chain] monotoneD[OF mono])

  define fq where "fq = (\<lambda>x. fun_sampler (Sup (q x ` Y)))"
  define tq where "tq = (\<lambda>x y. ptree_of_sampler (q x y))"
  have q_eq: "q x y = map_sampler (fq x) (sampler_of_ptree (tq x y))" if "y \<in> Y" for x y
    using comp that unfolding fq_def tq_def
    by (subst sampler_decompose_set [symmetric]) auto

  show "(\<Squnion>y\<in>Y. p \<bind> (\<lambda>x. q x y)) \<le> p \<bind> (\<lambda>x. \<Squnion> (q x ` Y))"
    by (intro Sup_sampler_least) (auto intro!: bind_sampler_mono Sup_sampler_upper comp)

  have "ptree_of_sampler (\<Squnion>y\<in>Y. p \<bind> (\<lambda>x. q x y)) =
          ptree_of_sampler (Sup ((\<lambda>y. sampler_of_ptree tp \<bind> (\<lambda>x. q (fp x) y)) ` Y))"
    by (simp add: p_eq map_conv_bind_sampler ptree_of_sampler_bind bind_assoc_sampler
             flip: Sup_ptree_of_sampler)
  also have "\<dots> = \<Squnion> (ptree_of_sampler ` (\<lambda>y. sampler_of_ptree tp \<bind> (\<lambda>x. q (fp x) y)) ` Y)"
    by (intro Sup_ptree_of_sampler [symmetric] chain_imp_compatible_sampler 
              chain_imageI[OF chain] bind_sampler_mono order.refl monotoneD[OF mono])
  also have "\<dots> = Sup (bind_ptree tp ` (\<lambda>x y. ptree_of_sampler (q (fp y) x)) ` Y)"
    by (simp add: ptree_of_sampler_bind image_image)
  also have "\<dots> = bind_ptree tp (\<lambda>y. \<Squnion>x\<in>Y. ptree_of_sampler (q (fp y) x))"
    by (intro Sup_bind_ptree2[OF chain] monotoneI ptree_of_sampler_mono monotoneD[OF mono])
  also have "\<dots> = ptree_of_sampler (p \<bind> (\<lambda>x. \<Squnion> (q x ` Y)))"
    apply (simp add: p_eq bind_map_sampler ptree_of_sampler_bind)
    apply (subst Sup_ptree_of_sampler [symmetric])
     apply (intro chain_imp_compatible_sampler chain_imageI[OF chain] monotoneD[OF mono])
     apply (simp_all add: image_image)
    done
  finally show "ptree_of_sampler (\<Squnion>y\<in>Y. p \<bind> (\<lambda>x. q x y)) =
                ptree_of_sampler (p \<bind> (\<lambda>x. \<Squnion> (q x ` Y)))" .
qed

lemma mcont_map_sampler [cont_intro]:
  assumes "mcont lub ord Sup (\<le>) g"
  shows   "mcont lub ord Sup (\<le>) (\<lambda>x. map_sampler f (g x))"
proof (rule mcont2mcont[OF _ assms])
  show "mcont Sup (\<le>) Sup (\<le>) (map_sampler f)"
    by (auto intro!: map_sampler_mono monoI contI 
             simp: mcont_def Sup_map_sampler chain_imp_compatible_sampler)
qed

lemma mcont_bind_sampler1: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>y. bind_sampler y f)"
  apply (intro mcontI monoI bind_sampler_mono order.refl | assumption)+
  apply (rule contI)
  apply (subst Sup_bind_sampler1)
   apply (erule chain_imp_compatible_sampler)
  apply simp
  done

lemma mcont_bind_sampler [cont_intro]:
  assumes f: "mcont luba orda Sup (\<le>) f"
  and g: "\<And>y. mcont luba orda Sup (\<le>) (g y)"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. bind_sampler (f x) (\<lambda>y. g y x))"
proof(rule mcont2mcont'[OF _ _ f])
  fix z
  show "mcont Sup (\<le>) Sup (\<le>) (\<lambda>x. bind_sampler x (\<lambda>y. g y z))"
    by (rule mcont_bind_sampler1)
next
  fix x
  let ?f = "\<lambda>z. bind_sampler x (\<lambda>y. g y z)"
  have "monotone orda (\<le>) ?f"
    by (intro monotoneI bind_sampler_mono order.refl monotoneD[OF mcont_mono[OF g]])
  moreover have "cont luba orda Sup (\<le>) ?f"
  proof (rule contI)
    fix Y
    assume chain: "Complete_Partial_Order.chain orda Y" and Y: "Y \<noteq> {}"
    have "bind_sampler x (\<lambda>y. g y (luba Y)) = bind_sampler x (\<lambda>y. Sup (g y ` Y))"
      by (rule bind_sampler_cong)(simp_all add: mcont_contD[OF g chain Y])
    also have "\<dots> = Sup ((\<lambda>p. x \<bind> (\<lambda>y. g y p)) ` Y)" using chain
      by (rule Sup_bind_sampler2) (rule mcont_mono[OF g])
    finally show "bind_sampler x (\<lambda>y. g y (luba Y)) = \<dots>" .
  qed
  ultimately show "mcont luba orda Sup (\<le>) ?f" by(rule mcontI)
qed

lemma mcont_replicate_sampler [cont_intro]:
  assumes [cont_intro]: "mcont luba orda Sup (\<le>) f"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. replicate_sampler n (f x))"
  by (induction n) (auto intro!: cont_intro)

definition list_lub :: "('a set \<Rightarrow> 'a) \<Rightarrow> 'a list set \<Rightarrow> 'a list" where
  "list_lub lub X =
     (let n = the_elem (length ` X) in map (\<lambda>i. lub ((\<lambda>xs. xs ! i) ` X)) [0..<n])"

lemma list_sampler [cont_intro]:
  assumes "mcont luba orda (list_lub Sup) (list_all2 (\<le>)) f"
  shows   "mcont luba orda Sup (\<le>) (\<lambda>x. list_sampler (f x))"
proof (rule mcont2mcont[OF _ assms])
  let ?L = "(list_sampler :: 'b sampler list \<Rightarrow> 'b list sampler)"
  show "mcont (list_lub Sup) (list_all2 (\<le>)) Sup (\<le>) ?L"
  proof
    show "monotone (list_all2 (\<le>)) (\<le>) ?L"
    proof
      fix xs ys :: "'b sampler list"
      assume "list_all2 (\<le>) xs ys"
      thus "list_sampler xs \<le> list_sampler ys"
        by induction (auto intro!: bind_sampler_mono map_sampler_mono)
    qed
  next
    show "cont (list_lub Sup) (list_all2 (\<le>)) Sup (\<le>) ?L"
    proof
      fix Y :: "'b sampler list set"
      assume Y: "Y \<noteq> {}" "Complete_Partial_Order.chain (list_all2 (\<le>)) Y"
      obtain n where n: "\<forall>xs\<in>Y. length xs = n"
        sorry
      show "list_sampler (list_lub Sup Y) = \<Squnion> (list_sampler ` Y)"
        using Y n
      proof (induction n arbitrary: Y)
        case 0
        hence "Y = {[]}" by auto
        thus ?case
          by (auto simp: list_lub_def)
      next
        case (Suc n)
        define A B where "A = hd ` Y" and "B = tl ` Y"
        have "list_lub Sup Y = Sup A # list_lub Sup B"
          sorry
        also have "list_sampler \<dots> = \<Squnion> A \<bind> (\<lambda>x. map_sampler ((#) x) (list_sampler (list_lub Sup B)))"
          by simp
        also have "list_sampler (list_lub Sup B) = \<Squnion> (list_sampler ` B)"
          apply (rule Suc.IH) 
            apply auto
          sorry
        also have "\<Squnion> A \<bind> (\<lambda>x. map_sampler ((#) x) (\<Squnion> (list_sampler ` B))) = 
                   \<Squnion> ((\<lambda>(a,b). a \<bind> (\<lambda>x. map_sampler ((#) x) (list_sampler b))) ` (A \<times> B))"
          sorry
        also have "\<dots> = \<Squnion> (list_sampler ` Y)"
          sorry
        finally show "list_sampler (list_lub Sup Y) = \<Squnion> (list_sampler ` Y)" .
      qed
    qed
  qed
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

lemma prob_ptree_singleton:
  "ptree.prob t {Some bs} = (if bs \<in> set_ptree t then 1 / 2 ^ length bs else 0)"
proof -
  have "{Some bs} = Some ` {bs}"
    by auto
  also have "ptree.prob t \<dots> = coin_space.prob {bs'. sprefix bs bs' \<and> bs \<in> set_ptree t}"
    by (subst prob_ptree) auto
  also have "{bs'. sprefix bs bs' \<and> bs \<in> set_ptree t} =
             (if bs \<in> set_ptree t then stake (length bs) -` {bs} else {})"
    by (auto simp: sprefix_def)
  also have "coin_space.prob \<dots> = (if bs \<in> set_ptree t then 1 / 2 ^ length bs else 0)"
    using prob_coin_space_stake[of "{bs}" "length bs"] by auto
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

lemma measure_pmf_of_ptree: "measure_pmf (spmf_of_ptree t) = measure_ptree t"
  by (simp add: spmf_of_ptree.rep_eq)

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



lift_definition coin_sampler :: "bool sampler" is
  "\<lambda>bs. Some (shd bs, 1)"
  by (auto simp: wf_pmfsr_def)

lemma run_sampler_coin [simp]: "run_sampler coin_sampler bs = Some (shd bs, 1)"
  by transfer auto

lemma coin_sampler_altdef: "coin_sampler = map_sampler hd (sampler_of_ptree (ptree_of_length 1))"
  by (rule sampler_eqI) (auto simp: run_sampler_of_ptree)






definition spmf_of_sampler' :: "'a sampler \<Rightarrow> ('a \<times> nat) spmf" where
  "spmf_of_sampler' p = map_spmf (\<lambda>bs. (fun_sampler p bs, length bs)) (spmf_of_ptree (ptree_of_sampler p))"

lemma spmf_spmf_of_sampler':
  "spmf (spmf_of_sampler' p) xn = coin_space.prob (run_sampler p -` {Some xn})"
proof -
  define t where "t = ptree_of_sampler p"
  define f where "f = fun_sampler p"
  have p_eq: "p = map_sampler f (sampler_of_ptree t)"
    by (simp add: f_def t_def flip: sampler_decompose)

  have "spmf (spmf_of_sampler' p) xn = ptree.prob t (Some ` (\<lambda>bs. (f bs, length bs)) -` {xn})"
    by (simp add: spmf_of_sampler'_def spmf_map measure_measure_spmf_conv_measure_pmf
                  measure_pmf_of_ptree t_def f_def)
  also have "\<dots> = coin_space.prob (Collect (\<lambda>bs'. \<exists>bs\<in>set_ptree t. sprefix bs bs' \<and> f bs = fst xn \<and> length bs = snd xn))"
    unfolding prob_ptree by (rule arg_cong[of _ _ coin_space.prob]) auto
  also have "Collect (\<lambda>bs'. \<exists>bs\<in>set_ptree t. sprefix bs bs' \<and> f bs = fst xn \<and> length bs = snd xn) =
             Collect (\<lambda>bs'.  run_sampler p bs' = Some xn)"
    by (intro arg_cong[of _ _ Collect] ext)
       (auto simp: p_eq run_sampler_of_ptree prefix_of_ptree_simps)
  finally show ?thesis by (simp add: vimage_def)
qed

lemma spmf_of_sampler'_welldefined:
  assumes "p = map_sampler f (sampler_of_ptree t)"
  shows   "spmf_of_sampler' p = map_spmf (\<lambda>bs. (f bs, length bs)) (spmf_of_ptree t)"
proof -
  have "spmf_of_sampler' p = map_spmf (\<lambda>bs. (fun_sampler p bs, length bs)) (spmf_of_ptree (ptree_of_sampler p))"
    by (simp add: spmf_of_sampler'_def o_def)
  also have "ptree_of_sampler p = t"
    using assms by simp
  also have "map_spmf (\<lambda>bs. (fun_sampler p bs, length bs)) (spmf_of_ptree t) = 
             map_spmf (\<lambda>bs. (f bs, length bs)) (spmf_of_ptree t)"
    by (rule map_spmf_cong) (auto simp: assms fun_sampler_map)
  finally show ?thesis by simp
qed

lemma spmf_of_samler'_bot [simp]: "spmf_of_sampler' bot = return_pmf None"
  by (simp add: spmf_of_sampler'_def)

lemma spmf_of_sampler'_return [simp]:
  "spmf_of_sampler' (return_sampler x) = return_spmf (x, 0)"
  by (subst spmf_of_sampler'_welldefined[of _ "\<lambda>_. x" "singleton_ptree []"]) auto

lemma spmf_of_sampler'_map [simp]:
  "spmf_of_sampler' (map_sampler f p) = map_spmf (map_prod f id) (spmf_of_sampler' p)"
proof (cases p)
  case (1 g t)
  show ?thesis
  proof (subst (1 2) spmf_of_sampler'_welldefined)
    show "p = map_sampler g (sampler_of_ptree t)"
      by fact
    show "map_sampler f p = map_sampler (f \<circ> g) (sampler_of_ptree t)"
      using 1 by (simp add: map_map_sampler)
  qed (auto simp: spmf.map_comp o_def)
qed

lemma spmf_of_sampler'_of_ptree [simp]:
  "spmf_of_sampler' (sampler_of_ptree t) = map_spmf (\<lambda>bs. (bs, length bs)) (spmf_of_ptree t)"
  by (subst spmf_of_sampler'_welldefined[of _ id t]) auto

lemma spmf_of_sampler'_coin [simp]:
  "spmf_of_sampler' coin_sampler = map_spmf (\<lambda>b. (b, 1)) coin_spmf" (is "?lhs = ?rhs")
proof (rule spmf_eqI)
  fix bn :: "bool \<times> nat"
  obtain b n where [simp]: "bn = (b, n)"
    by (cases bn)
  have "spmf ?lhs bn = (if n = 1 then coin_space.prob (shd -` {b}) else 0)"
    by (auto simp: spmf_spmf_of_sampler' vimage_def)
  also have "coin_space.prob (shd -` {b}) = 1/2"
    by (subst prob_coin_space_shd) auto
  finally have *: "spmf ?lhs bn = (if n = 1 then 1 / 2 else 0)" .

  have "spmf ?rhs bn = card ((\<lambda>b. (b, 1)) -` {(b, n)}) / 2"
    by (subst spmf_map) (auto simp: measure_spmf_spmf_of_set measure_pmf_of_set)
  also have "((\<lambda>b. (b, 1)) -` {(b, n)}) = (if n = 1 then {b} else {})"
    by auto
  finally have "spmf ?rhs bn = (if n = 1 then 1 / 2 else 0)"
    by auto
  with * show "spmf ?lhs bn = spmf ?rhs bn"
    by (simp only: )
qed

lemma measure_pmf_spmf_of_sampler':
  "measure_pmf (spmf_of_sampler' p) = distr coin_space (count_space UNIV) (run_sampler p)"
proof (cases p)
  case (1 f t)
  show ?thesis
    by (simp add: spmf_of_sampler'_welldefined[OF 1] 1 run_sampler_of_ptree o_assoc map_option.comp
                  map_pmf_rep_eq distr_distr o_def option.map_comp spmf_of_ptree.rep_eq measure_ptree_def)
qed



definition spmf_of_sampler :: "'a sampler \<Rightarrow> 'a spmf" where
  "spmf_of_sampler p = map_spmf fst (spmf_of_sampler' p)"

definition spmf_sampler_cost :: "'a sampler \<Rightarrow> nat spmf" where
  "spmf_sampler_cost p = map_spmf snd (spmf_of_sampler' p)"

lemma spmf_of_sampler_bot [simp]: "spmf_of_sampler bot = return_pmf None"
  and spmf_sampler_cost_bot [simp]: "spmf_sampler_cost bot = return_pmf None"
  by (simp_all add: spmf_of_sampler_def spmf_sampler_cost_def)

lemma spmf_of_sampler_return [simp]: "spmf_of_sampler (return_sampler x) = return_spmf x"
  and spmf_sampler_cost_return [simp]: "spmf_sampler_cost (return_sampler x) = return_spmf 0"
  by (simp_all add: spmf_of_sampler_def spmf_sampler_cost_def)

lemma spmf_of_sampler_coin [simp]: "spmf_of_sampler coin_sampler = coin_spmf"
  and spmf_sampler_cost_coin [simp]: "spmf_sampler_cost coin_sampler = return_spmf 1"
  by (simp_all add: spmf_of_sampler_def spmf_sampler_cost_def spmf.map_comp o_def
                    map_const_spmf_of_set)

lemma spmf_of_sampler_of_ptree [simp]:
        "spmf_of_sampler (sampler_of_ptree t) = spmf_of_ptree t"
  and spmf_sampler_cost_of_ptree [simp]:
        "spmf_sampler_cost (sampler_of_ptree t) = map_spmf length (spmf_of_ptree t)"
  by (simp_all add: spmf_of_sampler_def spmf_sampler_cost_def spmf.map_comp o_def)

lemma spmf_of_sampler_map [simp]:
        "spmf_of_sampler (map_sampler f p) = map_spmf f (spmf_of_sampler p)"
  and spmf_sampler_cost_map [simp]:
        "spmf_sampler_cost (map_sampler f p) = spmf_sampler_cost p"
  by (simp_all add: spmf_of_sampler_def spmf_sampler_cost_def spmf.map_comp o_def)

lemma spmf_of_sampler'_bind_aux:
  "spmf_of_sampler' (do {bs \<leftarrow> sampler_of_ptree t; bs' \<leftarrow> sampler_of_ptree (t' bs); return_sampler (bs, bs')}) =
     do {bs \<leftarrow> spmf_of_ptree t; bs' \<leftarrow> spmf_of_ptree (t' bs); return_spmf ((bs, bs'), length bs + length bs')}" 
  (is "?lhs = ?rhs")
proof (rule spmf_eqI)
  fix z :: "(bool list \<times> bool list) \<times> nat"
  obtain bs bs' n where [simp]: "z = ((bs, bs'), n)"
    by (metis apfst_convE)
  define P where "P = (n = length bs + length bs' \<and> bs \<in> set_ptree t \<and> bs' \<in> set_ptree (t' bs))"
  have "spmf ?lhs z = coin_space.prob
          (run_sampler (sampler_of_ptree t \<bind> (\<lambda>bs. map_sampler (Pair bs)
             (sampler_of_ptree (t' bs)))) -` {Some ((bs, bs'), n)})" (is "_ = coin_space.prob ?A")
    unfolding map_conv_bind_sampler [symmetric] by (simp add: spmf_spmf_of_sampler')
  also have "?A = (if P then {bs''. sprefix (bs @ bs') bs''} else {})"
    by (auto simp: run_sampler_bind run_sampler_of_ptree Option_bind_conv_case P_def
                   prefix_of_ptree_simps sprefix_append dest: set_ptree_sprefixD
             split: option.splits)+
  also have "{bs''. sprefix (bs @ bs') bs''} = stake (length bs + length bs') -` {bs @ bs'}"
    by (auto simp: sprefix_def)
  also have "coin_space.prob (if P then \<dots> else {}) =
               (if P then coin_space.prob (stake n -` {bs @ bs'}) else 0)"
    by (auto simp: P_def)
  also have "\<dots> = (if P then 1 / 2 ^ n else 0)"
    by (rule if_cong; (subst prob_coin_space_stake)?) (auto simp: P_def)
  finally have lhs: "spmf ?lhs z = (if P then 1 / 2 ^ n else 0)" .

  have rhs: "spmf ?rhs z = (if P then 1 / 2 ^ n else 0)"
  proof (cases P)
    case False
    hence "z \<notin> set_spmf ?rhs"
      by (auto simp: P_def set_bind_spmf)
    hence "spmf ?rhs z = 0"
      by (simp add: spmf_eq_0_set_spmf)
    with False show ?thesis
      by simp
  next
    case True
    define p where "p = coin_space.prob (stake (length bs') -` {bs'})"
    have "spmf ?rhs z = (LINT x|measure_spmf (spmf_of_ptree t).
            coin_space.prob {bs''. sprefix bs' bs'' \<and> bs' \<in> set_ptree (t' x) \<and> x = bs \<and> length x = length bs})"
      (is "_ = lebesgue_integral _ (\<lambda>x. coin_space.prob (?A x))")
      using True unfolding map_spmf_conv_bind_spmf [symmetric] P_def
      by (simp add: measure_measure_spmf_conv_measure_pmf spmf_bind conj_commute 
                    spmf_map measure_pmf_of_ptree prob_ptree)
    also have "?A = (\<lambda>x. if x = bs then stake (length bs') -` {bs'} else {})"
      using True by (auto simp: P_def fun_eq_iff sprefix_def)
    also have "(\<lambda>x. coin_space.prob (\<dots> x)) = (\<lambda>x. indicator {bs} x * p)"
      by (auto simp: p_def)
    also have "(LINT x|measure_spmf (spmf_of_ptree t). \<dots> x) = p / 2 ^ length bs"
      using True by (simp add: measure_measure_spmf_conv_measure_pmf prob_ptree_singleton
                               measure_pmf_of_ptree P_def)
    also have "\<dots> = 1 / 2 ^ n"
      using True unfolding p_def P_def by (subst prob_coin_space_stake) (auto simp: power_add)
    finally show ?thesis
      using True by auto
  qed

  from lhs and rhs show "spmf ?lhs z = spmf ?rhs z"
    by (simp only: )
qed

lemma spmf_of_sampler'_bind [simp]:
  "spmf_of_sampler' (bind_sampler p q) =
     do {(x, m) \<leftarrow> spmf_of_sampler' p; (y, n) \<leftarrow> spmf_of_sampler' (q x); return_spmf (y, m + n)}"
proof -
  define fp tp where "fp = fun_sampler p" and "tp = ptree_of_sampler p"
  define fq tq where "fq = fun_sampler \<circ> q" and "tq = ptree_of_sampler \<circ> q"
  have pq_eq: "p = map_sampler fp (sampler_of_ptree tp)"
              "q = (\<lambda>x. map_sampler (fq x) (sampler_of_ptree (tq x)))"
    by (simp_all add: fp_def tp_def fq_def tq_def flip: sampler_decompose)
  show ?thesis
    by (simp add: pq_eq bind_sampler_decompose spmf_of_sampler'_bind_aux map_spmf_conv_bind_spmf)
qed
  
lemma spmf_of_sampler_bind [simp]:
        "spmf_of_sampler (bind_sampler p q) = bind_spmf (spmf_of_sampler p) (spmf_of_sampler \<circ> q)"
  and spmf_sampler_cost_bind:
        "spmf_sampler_cost (bind_sampler p q) =
           do {(x,m) \<leftarrow> spmf_of_sampler' p; map_spmf ((+) m) (spmf_sampler_cost (q x))}"
  by (simp_all add: spmf_of_sampler_def spmf_sampler_cost_def
                    map_spmf_conv_bind_spmf case_prod_unfold)

lemma set_spmf_of_sampler':
  "set_spmf (spmf_of_sampler' p) = Some -` range (run_sampler p)"
  sorry


lemma set_spmf_of_sampler [simp]: "set_spmf (spmf_of_sampler p) = range_sampler p"
  unfolding spmf_of_sampler_def
  by (simp add: set_spmf_of_sampler' range_sampler_altdef)

lemma range_sampler_bind [simp]:
  "range_sampler (bind_sampler p q) = (\<Union>x\<in>range_sampler p. range_sampler (q x))"
proof -
  have "range_sampler (bind_sampler p q) = set_spmf (spmf_of_sampler (bind_sampler p q))"
    by (rule set_spmf_of_sampler [symmetric])
  also have "\<dots> = (\<Union>x\<in>range_sampler p. range_sampler (q x))"
    by (subst spmf_of_sampler_bind) (auto simp: set_bind_spmf)
  finally show ?thesis .
qed
  
lemma bind_sampler_eq_bot_iff:
  "bind_sampler p q = bot \<longleftrightarrow> p = bot \<or> (\<forall>x\<in>range_sampler p. q x = bot)"
  by (auto simp flip: range_sampler_empty_iff)


definition lossless_sampler :: "'a sampler \<Rightarrow> bool" where
  "lossless_sampler p \<longleftrightarrow> lossless_spmf (spmf_of_sampler p)"

lemma not_lossless_sampler_bot [simp]: "\<not>lossless_sampler bot"
  by (auto simp: lossless_sampler_def)

lemma lossless_sampler_return [simp, intro]: "lossless_sampler (return_sampler x)"
  by (auto simp: lossless_sampler_def)

lemma lossless_sampler_map_iff [simp]:
  "lossless_sampler (map_sampler f p) \<longleftrightarrow> lossless_sampler p"
  by (auto simp: lossless_sampler_def)

lemma lossless_sampler_bind_iff:
  "lossless_sampler (bind_sampler p q) \<longleftrightarrow>
     lossless_sampler p \<and> (\<forall>x\<in>range_sampler p. lossless_sampler (q x))"
  by (auto simp: lossless_sampler_def)

lemma lossless_sampler_list_iff:
  "lossless_sampler (list_sampler ps) \<longleftrightarrow> (\<forall>p\<in>set ps. lossless_sampler p)"
  by (induction ps) (auto simp: lossless_sampler_bind_iff range_sampler_empty_iff)

lemma lossless_sampler_replicate_iff:
  "lossless_sampler (replicate_sampler n p) \<longleftrightarrow> n = 0 \<or> lossless_sampler p"
  by (induction n) (auto simp: lossless_sampler_bind_iff)

lemma replicate_sampler_bot: "replicate_sampler n bot = (if n = 0 then return_sampler [] else bot)"
  by (cases n) auto

lemma replicate_sampler_bot' [simp]: "n > 0 \<Longrightarrow> replicate_sampler n bot = bot"
  by (cases n) auto

lemma list_sampler_bot: "bot \<in> set ps \<Longrightarrow> list_sampler ps = bot"
  by (induction ps) auto

lemma list_sampler_mono:
  assumes "list_all2 (\<le>) ps qs"
  shows   "list_sampler ps \<le> list_sampler qs"
  using assms by induction (auto intro!: bind_sampler_mono map_sampler_mono)

lemma relicate_sampler_mono:
  assumes [transfer_rule]: "p \<le> q"
  shows   "replicate_sampler n p \<le> replicate_sampler n q"
proof -
  have "list_all2 (\<le>) (replicate n p) (replicate n q)"
    by transfer_prover
  thus ?thesis
    unfolding list_sampler_replicate [symmetric] by (rule list_sampler_mono)
qed





definition loss_sampler where "loss_sampler p = pmf (spmf_of_sampler p) None"

lemma loss_sampler_01: "loss_sampler p \<in> {0..1}"
  unfolding loss_sampler_def by (auto simp: pmf_le_1)

lemma loss_sampler_bot [simp]: "loss_sampler bot = 1"
  by (auto simp: loss_sampler_def)

lemma loss_sampler_return [simp]: "loss_sampler (return_sampler x) = 0"
  by (auto simp: loss_sampler_def)

lemma loss_sampler_coin [simp]: "loss_sampler coin_sampler = 0"
  by (auto simp: loss_sampler_def)

lemma pmf_map_spmf_None [simp]: "pmf (map_spmf f p) None = pmf p None"
proof -
  have "pmf (map_spmf f p) None = measure_pmf.prob p (map_option f -` {None})"
    by (auto simp: pmf_map )
  also have "map_option f -` {None} = {None}"
    by auto
  also have "measure_pmf.prob p \<dots> = pmf p None"
    by (simp add: pmf.rep_eq)
  finally show ?thesis .
qed

lemma loss_sampler_map [simp]: "loss_sampler (map_sampler f p) = loss_sampler p"
  by (auto simp: loss_sampler_def)

lemma loss_sampler_bind:
  "loss_sampler (bind_sampler p q) =
     loss_sampler p + (LINT x|measure_spmf (spmf_of_sampler p). loss_sampler (q x))"
  by (auto simp: loss_sampler_def pmf_bind_spmf_None)




definition run_sampler' where
  "run_sampler' p bs = map_option (map_prod id (\<lambda>n. sdrop n bs)) (run_sampler p bs)"

definition measure_sampler' :: "'a sampler \<Rightarrow> ('a \<times> bool stream) option measure" where
  "measure_sampler' p =
     distr coin_space (option_measure (count_space UNIV \<Otimes>\<^sub>M coin_space)) (run_sampler' p)"






lemma spmf_of_sampler'_mono:
  assumes "p \<le> q"
  shows   "ord_spmf (=) (spmf_of_sampler' p) (spmf_of_sampler' q)"
proof (rule ord_pmf_increaseI)
  fix xn :: "'a \<times> nat"
  obtain x n where [simp]: "xn = (x, n)"
    by (cases xn)
  show "spmf (spmf_of_sampler' p) xn \<le> spmf (spmf_of_sampler' q) xn"
    using assms unfolding spmf_spmf_of_sampler'
    by (intro coin_space.finite_measure_mono vimage_mono' 
                 measurable_sets_coin_space[OF measurable_run_sampler])
       (auto dest: le_samplerD1)
qed auto

lemma map_spmf_mono':
  assumes "ord_spmf R p q" "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
  shows   "ord_spmf S (map_spmf f p) (map_spmf f q)"
  using assms unfolding ord_spmf_map_spmf12 by (rule ord_spmf_mono)

lemma spmf_of_sampler_mono:
  assumes "p \<le> q"
  shows   "ord_spmf (=) (spmf_of_sampler p) (spmf_of_sampler q)"
  unfolding spmf_of_sampler_def by (rule map_spmf_mono' spmf_of_sampler'_mono assms)+ simp_all

lemma lub_spmf_of_sampler':
  assumes "Complete_Partial_Order.chain (\<le>) Y"
  shows   "lub_spmf (spmf_of_sampler' ` Y) = spmf_of_sampler' (Sup Y)"
proof -
  define Y' where "Y' = ptree_of_sampler ` Y"
  define f where "f = fun_sampler (Sup Y)"
  define f' where "f' = (\<lambda>bs. (f bs, length bs))"
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

  have "lub_spmf (spmf_of_sampler' ` Y) = lub_spmf (map_spmf f' ` spmf_of_ptree ` Y')"
    by (simp add: Y image_image spmf.map_comp o_def f'_def)
  also have "\<dots> = map_spmf f' (lub_spmf (spmf_of_ptree ` Y'))"
    by (rule map_lub_spmf [symmetric] chain_imageI[OF chain_Y'] spmf_of_ptree_mono)+
  also have "lub_spmf (spmf_of_ptree ` Y') = spmf_of_ptree (Sup Y')"
    using chain_Y' by (rule spmf_of_ptree_Sup [symmetric])
  also have "map_spmf f' (spmf_of_ptree (\<Squnion> Y')) =
             spmf_of_sampler' (map_sampler f (sampler_of_ptree (\<Squnion>Y')))"
    by (simp add: spmf.map_comp o_def f'_def)
  also have "map_sampler f (sampler_of_ptree (\<Squnion>Y')) = \<Squnion>Y"
    by (simp add: Sup_map_sampler Y chain_Y' compatible_sampler_of_ptree 
                  ptree_chain_imp_compatible sampler_of_ptree_Sup)
  finally show ?thesis .
qed

lemma lub_spmf_of_sampler:
  assumes "Complete_Partial_Order.chain (\<le>) Y"
  shows   "lub_spmf (spmf_of_sampler ` Y) = spmf_of_sampler (Sup Y)"
proof -
  have "lub_spmf (spmf_of_sampler ` Y) = lub_spmf (map_spmf fst ` spmf_of_sampler' ` Y)"
    by (simp add: image_image spmf_of_sampler_def)
  also have "\<dots> = map_spmf fst (lub_spmf (spmf_of_sampler' ` Y))"
    by (rule map_lub_spmf [symmetric])
       (use assms  in \<open>auto intro: chain_imageI spmf_of_sampler'_mono\<close>)
  also have "\<dots> = spmf_of_sampler (Sup Y)"
    using assms by (simp add: lub_spmf_of_sampler' spmf_of_sampler_def)
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

abbreviation "mono_sampler \<equiv> monotone (fun_ord ((\<le>) :: 'a sampler \<Rightarrow> _)) ((\<le>) :: 'b sampler \<Rightarrow> _)"

lemma map_sampler_mono' [partial_function_mono]: 
  "mono_sampler B \<Longrightarrow> mono_sampler (\<lambda>g. map_sampler f (B g))"
  by (auto simp: monotone_def fun_ord_def intro: map_sampler_mono)

lemma bind_sampler_mono' [partial_function_mono]:
  assumes mf: "mono_sampler B" and mg: "\<And>y. mono_sampler (\<lambda>f. C y f)"
  shows "mono_sampler (\<lambda>f. bind_sampler (B f) (\<lambda>y. C y f))"
  using assms by (auto simp: monotone_def fun_ord_def intro: bind_sampler_mono)


(* TODO *)
consts bernoulli_sampler :: "real \<Rightarrow> bool sampler"

definition bernoulli_spmf where "bernoulli_spmf p = spmf_of_pmf (bernoulli_pmf p)"


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
  "rel_spmf_sampler coin_spmf coin_sampler"
  by (auto simp: rel_spmf_sampler_def rel_fun_def)

lemma rel_sampler_bernoulli [transfer_rule]:
  "((=) ===> rel_spmf_sampler) bernoulli_spmf bernoulli_sampler"
  sorry

end




declare [[function_internals]]

partial_function (spmf) foo :: "real \<Rightarrow> nat spmf"
  where "foo p = do {b \<leftarrow> bernoulli_spmf p; if b then return_spmf 0 else map_spmf Suc (foo (p / 2))}"
print_theorems

partial_function (sampler) foos :: "real \<Rightarrow> nat sampler"
  where "foos p = do {b \<leftarrow> bernoulli_sampler p; if b then return_sampler 0 else map_sampler Suc (foos (p / 2))}"
print_theorems

thm foo_def foos_def


partial_function (spmf) bar :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat spmf"
  where "bar p q r = do {b \<leftarrow> bernoulli_spmf (p + q + r); if b then return_spmf 0 else map_spmf Suc (bar p q r)}"
print_theorems
partial_function (sampler) bars :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat sampler"
  where "bars p q r = do {b \<leftarrow> bernoulli_sampler (p + q + r); if b then return_sampler 0 else map_sampler Suc (bars p q r)}"
print_theorems
thm bar_def bars_def


context includes lifting_syntax
begin

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

end




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

end



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

partial_function (sampler) bernoulli_sampler' :: "real \<Rightarrow> bool sampler" where
  "bernoulli_sampler' p =
     do {b \<leftarrow> coin_sampler;
         if b then
           return_sampler (p \<ge> 1/2)
         else
           bernoulli_sampler' (if p < 1/2 then 2 * p else 2 * p - 1)}"





lemmas [code] = bernoulli_sampler'.simps

value [code] "run_sampler (bernoulli_sampler' (1/3)) (random_bits 1)"
value [code] "run_sampler (bernoulli_sampler' (1/3)) (random_bits 2)"
value [code] "run_sampler (bernoulli_sampler' (1/3)) (random_bits 8)"



partial_function (sampler) geometric_sampler :: "real \<Rightarrow> nat sampler" where
  "geometric_sampler p =
     do {b \<leftarrow> bernoulli_sampler' p;
         if b then return_sampler 0 else map_sampler Suc (geometric_sampler p)}"

lemmas [code] = geometric_sampler.simps


value [code] "run_sampler' (geometric_sampler (1/3)) (random_bits 1)"
value [code] "map (\<lambda>i. fst (the (run_sampler' (geometric_sampler (1/3)) (random_bits i)))) [0..<100]"


lemma loss_sampler_bernoulli [simp]: "loss_sampler (bernoulli_sampler' p) = 0"
proof -
  define f where "f = (\<lambda>p. loss_sampler (bernoulli_sampler' p))"
  have f_rec: "f p = f (if p < 1 / 2 then 2 * p else 2 * p - 1) / 2" for p
    unfolding f_def
    by (subst bernoulli_sampler'.simps)
       (simp_all add: loss_sampler_bind spmf_of_set_def integral_pmf_of_set UNIV_bool
                 del: spmf_of_pmf_pmf_of_set)
  have f_01: "f p \<in> {0..1}" for p
    using loss_sampler_01[of "bernoulli_sampler p"] by (auto simp: f_def)
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

lemma spmf_of_sampler_bernoulli [simp]:
  "spmf_of_sampler (bernoulli_sampler' p) = spmf_of_pmf (bernoulli_pmf p)"
  sorry


lemma loss_sampler_geometric [simp]:
  assumes "p \<in> {0<..1}"
  shows   "loss_sampler (geometric_sampler p) = 0"
proof -
  have "loss_sampler (geometric_sampler p) = loss_sampler (geometric_sampler p) * (1 - p)"
    using assms by (subst geometric_sampler.simps) (simp_all add: loss_sampler_bind)
  thus "loss_sampler (geometric_sampler p) = 0"
    using assms by (auto simp: algebra_simps)
qed



partial_function (sampler) while_sampler :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a sampler) \<Rightarrow> 'a \<Rightarrow> 'a sampler" where
  "while_sampler guard body s =
     (if guard s then return_sampler s else body s \<bind> while_sampler guard body)"

lemmas [code] = while_sampler.simps

value [code] "run_sampler (while_sampler (\<lambda>n::nat. n > 42) (\<lambda>n. map_sampler (\<lambda>b. of_bool b + 2 * n) coin_sampler) 0) (random_bits 0)"
value [code] "run_sampler (while_sampler (\<lambda>n::nat. n > 42) (\<lambda>n. map_sampler (\<lambda>b. of_bool b + 2 * n) coin_sampler) 0) (random_bits 4)"
value [code] "run_sampler (while_sampler (\<lambda>n::nat. n > 42) (\<lambda>n. map_sampler (\<lambda>b. of_bool b + 2 * n) coin_sampler) 0) (random_bits 5)"



datatype 'a mytree = Node 'a "'a mytree list"

partial_function (sampler) foo :: "real \<Rightarrow> bool mytree sampler" where
  "foo p = do {
     b \<leftarrow> coin_sampler;
     n \<leftarrow> geometric_sampler p; map_sampler (\<lambda>xs. Node b xs) (replicate_sampler n (foo (2 * p)))}"

lemmas [code] = foo.simps

value [code] "run_sampler' (foo 0.1) (random_bits 1)"
value [code] "run_sampler' (foo 0.1) (random_bits 2)"
value [code] "run_sampler' (foo 0.1) (random_bits 3)"


context
  fixes n :: nat
begin

partial_function (sampler) fast_dice_roll :: "nat \<Rightarrow> nat \<Rightarrow> nat sampler"
where
  "fast_dice_roll v c = 
  (if v \<ge> n then if c < n then return_sampler c else fast_dice_roll (v - n) (c - n)
   else do {
     b \<leftarrow> coin_sampler;
     fast_dice_roll (2 * v) (2 * c + (if b then 1 else 0)) } )"

definition fast_uniform :: "nat sampler"
  where "fast_uniform = fast_dice_roll 1 0"

end

lemmas [code] = fast_dice_roll.simps

value [code] "run_sampler' (fast_uniform 10) ([True, False, True, True, False] @- sconst False)"
value [code] "run_sampler' (fast_uniform 10) ([False, False, True, True, False] @- sconst False)"
value [code] "run_sampler' (fast_uniform 10) ([True, False, True, False, False] @- sconst False)"
value [code] "run_sampler' (fast_uniform 10) ([True, False, True, True, True] @- sconst False)"
value [code] "run_sampler' (fast_uniform 10) ([True, False, True, True, False, True, True, False, True] @- sconst False)"
value [code] "run_sampler' (fast_uniform 10) ([True, True, True, True, True, True, False, True, True] @- sconst False)"
value [code] "map (\<lambda>i. fst (the (run_sampler' (fast_uniform 10) (random_bits i)))) [0..<100]"
value [code] "run_sampler' (replicate_sampler 100 (fast_uniform 10)) (random_bits 0)"
value [code] "run_sampler' (replicate_sampler 100 (fast_uniform 10)) (random_bits 43)"
value [code] "run_sampler (consumption_sampler (replicate_sampler 100 (fast_uniform 10))) (random_bits 43)"

end