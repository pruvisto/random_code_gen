theory PMF_Sampler
  imports Main "HOL-Probability.Probability" "HOL-Library.Code_Lazy"
begin

lemma Option_bind_conv_case: "Option.bind x f = (case x of None \<Rightarrow> None | Some x \<Rightarrow> f x)"
  by (auto split: option.splits)

lemma stake_shift:
  "stake m (xs @- ys) = (if m \<le> length xs then take m xs else xs @ stake (m - length xs) ys)"
proof (induction m arbitrary: xs)
  case (Suc m xs)
  thus ?case
    by (cases xs) auto
qed auto

lemma stake_shift_small [simp]: "m \<le> length xs \<Longrightarrow> stake m (xs @- ys) = take m xs"
  and stake_shift_big [simp]: "m \<ge> length xs \<Longrightarrow> stake m (xs @- ys) = xs @ stake (m - length xs) ys"
  by (subst stake_shift; simp)+

lemma sdrop_shift:
  "sdrop m (xs @- ys) = (if m \<le> length xs then drop m xs @- ys else sdrop (m - length xs) ys)"
proof (induction m arbitrary: xs)
  case (Suc m xs)
  thus ?case
    by (cases xs) auto
qed auto

lemma sdrop_shift_small [simp]: "m \<le> length xs \<Longrightarrow> sdrop m (xs @- ys) = drop m xs @- ys"
  and sdrop_shift_big [simp]: "m \<ge> length xs \<Longrightarrow> sdrop m (xs @- ys) = sdrop (m - length xs) ys"
  by (subst sdrop_shift; simp)+

definition coin_space :: "bool stream measure" where
  "coin_space = stream_space (measure_pmf (pmf_of_set UNIV))"

lemma space_coin_space: "space coin_space = UNIV"
  by (simp add: coin_space_def space_stream_space)

interpretation coin_space: prob_space coin_space
  unfolding coin_space_def
  by (intro prob_space.prob_space_stream_space prob_space_measure_pmf)

definition options :: "'a set \<Rightarrow> 'a option set" where
  "options X = insert None (Some ` X)" 

lemma None_in_options [simp]: "None \<in> options X"
  by (auto simp: options_def)

lemma Some_in_options_iff [simp]: "Some x \<in> options X \<longleftrightarrow> x \<in> X"
  by (auto simp: options_def)


definition option_algebra :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a option set set" where
  "option_algebra \<Omega> \<Sigma> = {X. Some -` X \<in> \<Sigma>} \<inter> Pow (options \<Omega>)"

lemma in_option_algebra_insert_None_iff [simp]:
  "insert None X \<in> option_algebra \<Omega> \<Sigma> \<longleftrightarrow> X \<in> option_algebra \<Omega> \<Sigma>"
proof -
  have "Some -` insert None X = Some -` X"
    by auto
  thus ?thesis
    by (simp add: option_algebra_def)
qed

lemma in_option_algebra_Some_image_iff [simp]:
  "Some ` X \<in> option_algebra \<Omega> \<Sigma> \<longleftrightarrow> X \<subseteq> \<Omega> \<and> X \<in> \<Sigma>"
proof -
  have "Some -` Some ` X = X"
    by auto
  thus ?thesis
    by (auto simp: option_algebra_def)
qed

lemma options_in_option_algebra_iff [simp]:
  "options X \<in> option_algebra \<Omega> \<Sigma> \<longleftrightarrow> X \<subseteq> \<Omega> \<and> X \<in> \<Sigma>"
  by (simp add: options_def)

lemma empty_in_option_algebra_iff [simp]: "{} \<in> option_algebra \<Omega> \<Sigma> \<longleftrightarrow> {} \<in> \<Sigma>"
  by (simp add: option_algebra_def)

lemma range_Some: "range Some = -{None}"
  using notin_range_Some by blast

lemma vimage_Some_insert_None [simp]: "Some -` insert None X = Some -` X"
  by auto


lemma (in sigma_algebra) option_algebra[intro]:
  "sigma_algebra (options \<Omega>) (option_algebra \<Omega> M)"
proof
  show "option_algebra \<Omega> M \<subseteq> Pow (options \<Omega>)"
    by (auto simp: options_def option_algebra_def)
  show "{} \<in> option_algebra \<Omega> M"
    by (auto simp: options_def option_algebra_def)
  show "X \<inter> Y \<in> option_algebra \<Omega> M" if "X \<in> option_algebra \<Omega> M" "Y \<in> option_algebra \<Omega> M" for X Y
    using that unfolding option_algebra_def options_def by auto
  show "\<exists>C\<subseteq>option_algebra \<Omega> M. finite C \<and> disjoint C \<and> X - Y = \<Union> C"
    if "X \<in> option_algebra \<Omega> M" "Y \<in> option_algebra \<Omega> M" for X Y
  proof -
    have "\<exists>C\<subseteq>M. finite C \<and> disjoint C \<and> Some -` X - Some -` Y = \<Union> C"
      by (intro Diff_cover) (use that in \<open>auto simp: option_algebra_def\<close>)
    then obtain C where C: "C \<subseteq> M" "finite C" "disjoint C" "Some -` X - Some -` Y = \<Union> C"
      by metis
    define C' where "C' = (if None \<in> X - Y then {{None}} else {}) \<union> (\<lambda>Z. Some ` Z) ` C"
    have "C' \<subseteq> option_algebra \<Omega> M"
      using C(1) sets_into_space unfolding option_algebra_def C'_def
      by (auto simp:  vimage_image_eq; blast)
    moreover have "finite C'"
      using C unfolding C'_def
      by (auto simp: inj_image_mem_iff[of Some])
    moreover have "disjoint C'"
      unfolding C'_def by (intro disjoint_union disjoint_image C) (auto simp: disjoint_def)
    moreover have "X - Y = \<Union> C'"
    proof -
      have "\<Union> C' = (if None \<in> X - Y then {None} else {}) \<union> Some ` \<Union> C"
        by (auto simp: C'_def)
      also have "\<Union> C = Some -` X - Some -` Y"
        using C(4) by simp
      also have "(if None \<in> X - Y then {None} else {}) \<union> Some ` \<dots> = X - Y"
        by (auto simp: image_set_diff range_Some)
      finally show ?thesis ..
    qed
    ultimately show ?thesis
      by blast
  qed
  show "X \<union> Y \<in> option_algebra \<Omega> M" if "X \<in> option_algebra \<Omega> M" "Y \<in> option_algebra \<Omega> M" for X Y
    using that unfolding option_algebra_def options_def by auto
  show "options \<Omega> \<in> option_algebra \<Omega> M"
    by simp
  show "\<Union> (range A) \<in> option_algebra \<Omega> M"
    if "range A \<subseteq> option_algebra \<Omega> M" for A :: "nat \<Rightarrow> 'a option set"
  proof -
    define A' where "A' = (\<lambda>n. Some -` A n)"
    have A': "range A' \<subseteq> M"
      using that by (auto simp: A'_def option_algebra_def)

    have "\<Union> (range A) = (if \<exists>n. None \<in> A n then {None} else {}) \<union> Some ` \<Union> (range A')"
      by (auto simp: A'_def image_UN range_Some)
    also have "\<dots> \<in> option_algebra \<Omega> M"
      using A' sets_into_space by auto
    finally show ?thesis .
  qed
qed

  
definition option_measure where
  "option_measure M = sigma (options (space M)) (option_algebra (space M) (sets M))" 

lemma space_option_measure: "space (option_measure M) = options (space M)"
  unfolding option_measure_def by (subst space_measure_of) (auto simp: option_algebra_def)

lemma sets_option_measure: "sets (option_measure M) = option_algebra (space M) (sets M)"
proof -
  interpret options: sigma_algebra "options (space M)" "option_algebra (space M) (sets M)" ..
  show ?thesis
  unfolding option_measure_def using options.sigma_sets_eq
    by (subst sets_measure_of) (simp_all add: option_algebra_def)
qed

lemma measurable_None [measurable]: "{None} \<in> sets (option_measure M)"
  by (simp add: sets_option_measure)

lemma measurable_Some [measurable]: "Some \<in> M \<rightarrow>\<^sub>M option_measure M"
  by (auto simp add: sets_option_measure measurable_def space_option_measure option_algebra_def)

lemma measurable_is_none [measurable]: "Option.is_none \<in> option_measure M \<rightarrow>\<^sub>M count_space UNIV"
  unfolding Measurable.pred_def
  by (auto simp: sets_option_measure space_option_measure options_def 
                 Option.is_none_def option_algebra_def)

lemma measurable_the [measurable]:
  "the \<in> restrict_space (option_measure M) (-{None}) \<rightarrow>\<^sub>M M"
  unfolding measurable_def
proof safe
  fix x assume "x \<in> space (restrict_space (option_measure M) (- {None}))"
  thus "the x \<in> space M"
    by (auto simp: space_restrict_space space_option_measure Option.the_def split: option.splits)
next
  fix X assume X: "X \<in> sets M"
  have "Some ` X \<in> (\<lambda>X. Some ` X) ` sets M"
    using X by blast
  also have "(\<lambda>X. Some ` X) ` sets M = (\<lambda>X. X \<inter> -{None}) ` sets (option_measure M)"
  proof safe
    fix Y assume "Y \<in> sets (option_measure M)"
    hence "Some -` Y \<in> sets M"
      by (auto simp: sets_option_measure option_algebra_def)
    moreover have "Some ` Some -` Y = Y \<inter> -{None}"
      by auto
    ultimately show "Y \<inter> - {None} \<in> (`) Some ` sets M"
      by blast
  next
    fix Y assume Y: "Y \<in> sets M"
    have "Some ` Y = Some ` Y \<inter> - {None}" "Some ` Y \<in> sets (option_measure M)"
      using Y sets.sets_into_space by (auto simp: sets_option_measure)
    thus "Some ` Y \<in> (\<lambda>Y. Y \<inter> - {None}) ` sets (option_measure M)"
      by blast
  qed
  also have "\<dots> = sets (restrict_space (option_measure M) (- {None}))"
    by (auto simp: sets_restrict_space sets_option_measure option_algebra_def options_def)
  also have "Some ` X = the -` X \<inter> space (restrict_space (option_measure M) (- {None}))"
    using X sets.sets_into_space
    by (auto simp: space_restrict_space space_option_measure options_def)
  finally show "the -` X \<inter> space (restrict_space (option_measure M) (- {None})) \<in>
                  sets (restrict_space (option_measure M) (- {None}))" .
qed

lemma measurable_case_option [measurable]:
  assumes f [measurable]: "f \<in> M \<rightarrow>\<^sub>M R"
  assumes g [measurable]: "(\<lambda>(x,y). g x y) \<in> M \<Otimes>\<^sub>M N \<rightarrow>\<^sub>M R"
  assumes h [measurable]: "h \<in> M \<rightarrow>\<^sub>M option_measure N"
  shows   "(\<lambda>x. case h x of None \<Rightarrow> f x | Some y \<Rightarrow> g x y) \<in> M \<rightarrow>\<^sub>M R"
proof -
  have "(\<lambda>x. if Option.is_none (h x) then f x else g x (the (h x))) \<in> M \<rightarrow>\<^sub>M R"
  proof (subst measurable_If_restrict_space_iff; safe?)
    show "{x \<in> space M. Option.is_none (h x)} \<in> sets M"
      by measurable
    show "f \<in> restrict_space M {x. Option.is_none (h x)} \<rightarrow>\<^sub>M R"
      by (rule measurable_restrict_space1) measurable
    have "(\<lambda>x. x) \<in> restrict_space M {x. \<not> Option.is_none (h x)} \<rightarrow>\<^sub>M M"
      by (rule measurable_restrict_space1) measurable
    moreover have "h \<in> restrict_space M {x. \<not> Option.is_none (h x)} \<rightarrow>\<^sub>M
                       restrict_space (option_measure N) (- {None})"
      by (rule measurable_restrict_space3) auto
    ultimately show "(\<lambda>x. g x (the (h x))) \<in> restrict_space M {x. \<not> Option.is_none (h x)} \<rightarrow>\<^sub>M R"
      by measurable
  qed
  also have "(\<lambda>x. if Option.is_none (h x) then f x else g x (the (h x))) =
             (\<lambda>x. case h x of None \<Rightarrow> f x | Some y \<Rightarrow> g x y)"
    by (auto split: option.splits simp: fun_eq_iff)
  finally show ?thesis .
qed

lemma countable_options [intro]:
  assumes "countable A"
  shows   "countable (options A)"
  using assms unfolding options_def by blast



type_synonym 'a pmfsr = "bool stream \<Rightarrow> ('a \<times> nat) option"

definition range_pmfsr where "range_pmfsr r = fst ` Some -` range r"

definition wf_pmfsr :: "'a pmfsr \<Rightarrow> bool" where
  "wf_pmfsr p \<longleftrightarrow>
     (\<forall>bs. case p bs of None \<Rightarrow> True | Some (x, n) \<Rightarrow>
       (\<forall>bs'. stake n bs' = stake n bs \<longrightarrow> p bs' = p bs))"


(*
definition wf_pmfsr :: "'a pmfsr \<Rightarrow> bool" where
  "wf_pmfsr r \<longleftrightarrow>
     r \<in> coin_space \<rightarrow>\<^sub>M count_space UNIV \<and>
     countable (range_pmfsr r) \<and>
     wf_pmfsr r"
*)



lemma in_range_pmfsrI:
  assumes "r bs = Some (y, n)"
  shows   "y \<in> range_pmfsr r"
proof -
  have "Some (y, n) \<in> range r"
    by (rule range_eqI[of _ _ bs]) (use assms in auto)
  thus ?thesis
    unfolding range_pmfsr_def
    by (intro image_eqI[of _ _ "(y, n)"]) (use assms in auto)
qed

lemma in_range_pmfsr: "r bs \<in> options (range_pmfsr r \<times> UNIV)"
proof (cases "r bs")
  case [simp]: (Some z)
  obtain y n where [simp]: "z = (y, n)"
    by (cases z)
  have "y \<in> range_pmfsr r"
    by (rule in_range_pmfsrI[of _ bs _ n]) auto
  thus ?thesis
    by auto
qed auto

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

lemma countable_range_pmfsr:
  assumes "wf_pmfsr r"
  shows   "countable (range_pmfsr r)"
proof -
  define f where "f = (\<lambda>bs. fst (the (r (bs @- sconst False))))"
  have "range_pmfsr r \<subseteq> range f"
  proof
    fix x assume "x \<in> range_pmfsr r"
    then obtain bs n where bs: "r bs = Some (x, n)"
      by (auto simp: range_pmfsr_def eq_commute)
    have "r (stake n bs @- sconst False) = Some (x, n)"
      by (rule wf_pmfsrD[OF assms bs]) auto
    hence "f (stake n bs) = x"
      by (auto simp: f_def)
    thus "x \<in> range f"
      by blast
  qed
  thus ?thesis
    by (rule countable_subset) auto
qed

lemma range_pmfsr_subset: "range r \<subseteq> options (range_pmfsr r \<times> UNIV)"
proof
  fix xn assume "xn \<in> range r"
  then obtain bs where [simp]: "r bs = xn"
    by (auto simp: eq_commute)
  show "xn \<in> options (range_pmfsr r \<times> UNIV)"
  proof (cases xn)
    case [simp]: (Some xn')
    obtain x n where [simp]: "xn' = (x, n)"
      by (cases xn')
    have "x \<in> range_pmfsr r"
      by (rule in_range_pmfsrI[of _ bs _ n]) auto
    thus ?thesis
      by auto
  qed auto
qed

lemma countable_range_pmfsr':
  assumes "wf_pmfsr r"
  shows   "countable (range r)"
proof (rule countable_subset)
  show "range r \<subseteq> options (range_pmfsr r \<times> UNIV)"
    by (rule range_pmfsr_subset)
  show "countable (options (range_pmfsr r \<times> (UNIV :: nat set)))"
    using countable_range_pmfsr[OF assms] by blast
qed

lemma measurable_pmfsr:
  assumes "wf_pmfsr r"
  shows   "r \<in> coin_space \<rightarrow>\<^sub>M count_space UNIV"
proof -
  have *: "r -` Some ` X \<in> sets coin_space" if X: "X \<subseteq> range_pmfsr r \<times> UNIV" for X
  proof -
    define A where "A = {bs |bs x. r (bs @- sconst False) = Some (x, length bs) \<and> (x, length bs) \<in> X}"
    have "(\<Union>bs\<in>A. stake (length bs) -` {bs} \<inter> space coin_space) \<in> sets coin_space"
    proof (rule sets.countable_UN'')
      show "stake (length bs) -` {bs} \<inter> space coin_space \<in> coin_space.events" for bs
        unfolding coin_space_def by measurable
    qed auto
    also have "(\<Union>bs\<in>A. stake (length bs) -` {bs} \<inter> space coin_space) = (\<Union>bs\<in>A. stake (length bs) -` {bs})"
      by (simp add: space_coin_space)
    also have "\<dots> = r -` Some ` X"
    proof safe
      fix bs x n
      assume *: "r bs = Some (x, n)" "(x, n) \<in> X"
      define bs' where "bs' = stake n bs"
      have **: "r (bs' @- sconst False) = Some (x, n)"
        by (rule wf_pmfsrD[OF assms *(1)]) (auto simp: bs'_def)
      from ** have "bs' \<in> A"
        using * by (auto simp: A_def bs'_def)
      moreover have "bs \<in> stake (length bs') -` {bs'}"
        by (auto simp: bs'_def)
      ultimately show "bs \<in> (\<Union>bs\<in>A. stake (length bs) -` {bs})"
        by blast
    next
      fix bs' bs
      assume bs': "bs' \<in> A" "stake (length bs') bs = bs'"
      define n where "n = length bs'"
      from bs'(1) obtain x where xn: "r (bs' @- sconst False) = Some (x, n)" "(x, n) \<in> X"
        unfolding A_def by (auto simp: n_def)
      have "r bs = Some (x, n)"
        by (rule wf_pmfsrD[OF assms xn(1)]) (use bs'(2) in \<open>auto simp: n_def\<close>)
      thus "bs \<in> r -` Some ` X"
        using xn by auto
    qed
    finally show ?thesis .
  qed

  have **: "r -` Some ` X \<in> sets coin_space" for X
  proof -
    have "r -` Some ` (X \<inter> (range_pmfsr r \<times> UNIV)) \<in> sets coin_space"
      by (intro *) auto
    also have "r -` Some ` (X \<inter> (range_pmfsr r \<times> UNIV)) = r -` Some ` X"
      by (auto simp add: in_range_pmfsrI)
    finally show ?thesis .
  qed

  have ***: "r -` X \<in> sets coin_space" if "None \<notin> X" for X
  proof -
    have "r -` Some ` Some -` X \<in> sets coin_space"
      by (intro **)
    also have "Some ` Some -` X = X"
      using that by (subst image_vimage_eq) (auto simp: range_Some)
    finally show ?thesis .
  qed

  show ?thesis
  proof (rule measurableI)
    show "r -` X \<inter> space coin_space \<in> sets coin_space" for X
    proof (cases "None \<in> X")
      case False
      thus ?thesis using *** by blast
    next
      case True
      hence "r -` (-X) \<in> sets coin_space"
        by (intro ***) auto
      hence "space coin_space - r -` (-X) \<in> sets coin_space"
        by blast
      also have "space coin_space - r -` (-X) = r -` X"
        by (auto simp: space_coin_space)
      finally show ?thesis
        by (simp add: space_coin_space)
    qed
  qed auto
qed


definition return_pmfsr :: "'a \<Rightarrow> 'a pmfsr" where
  "return_pmfsr x bs = Some (x, 0)"

definition coin_pmfsr :: "bool pmfsr" where
  "coin_pmfsr bs = Some (shd bs, 1)"

definition bind_pmfsr :: "'a pmfsr \<Rightarrow> ('a \<Rightarrow> 'b pmfsr) \<Rightarrow> 'b pmfsr" where
  "bind_pmfsr r f bs =
     do {(x, m) \<leftarrow> r bs; (y, n) \<leftarrow> f x (sdrop m bs); Some (y, m + n)}"

adhoc_overloading Monad_Syntax.bind bind_pmfsr

definition map_pmfsr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pmfsr \<Rightarrow> 'b pmfsr" where
  "map_pmfsr f r bs = map_option (map_prod f id) (r bs)"

lemma map_pmfsr_id [simp]: "map_pmfsr id r = r"
  by (auto simp: fun_eq_iff map_pmfsr_def return_pmfsr_def Option_bind_conv_case map_option_case
           split: option.splits)

lemma map_pmfsr_id' [simp]: "map_pmfsr (\<lambda>x. x) r = r"
  by (auto simp: fun_eq_iff map_pmfsr_def return_pmfsr_def Option_bind_conv_case map_option_case
           split: option.splits)

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

definition run_pmfsr :: "'a pmfsr \<Rightarrow> bool stream \<Rightarrow> ('a \<times> bool stream) option" where
  "run_pmfsr p bs = map_option (\<lambda>(x,n). (x, sdrop n bs)) (p bs)"

definition measure_pmfsr :: "'a pmfsr \<Rightarrow> 'a option measure" where
  "measure_pmfsr p = distr coin_space (count_space UNIV) (map_option fst \<circ> p)"

definition pmfsr_space :: "('a \<times> bool stream) option measure" where
  "pmfsr_space = option_measure (count_space UNIV \<Otimes>\<^sub>M coin_space)"

definition measure_pmfsr' :: "'a pmfsr \<Rightarrow> ('a \<times> bool stream) option measure" where
  "measure_pmfsr' p = distr coin_space pmfsr_space (run_pmfsr p)"

lemma stream_eqI: "(\<And>n. snth s n = snth s' n) \<Longrightarrow> s = s'"
proof (coinduction arbitrary: s s')
  case (Eq_stream s s')
  have *: "s !! n = s' !! n" for n
    using Eq_stream by auto
  from *[of 0] and *[of "Suc n" for n] show ?case
    by auto
qed

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
    apply (subst emeasure_coin_space)
    apply simp_all
    sorry
  also have "{x. True # stake n x \<in> A \<and> sdrop n x \<in> B} = {x. stake n x \<in> AT \<and> sdrop n x \<in> B}"
    by (auto simp: AT_def)
  also have "{x. False # stake n x \<in> A \<and> sdrop n x \<in> B} = {x. stake n x \<in> AF \<and> sdrop n x \<in> B}"
    by (auto simp: AF_def)
  also have "P {x. stake n x \<in> AT \<and> sdrop n x \<in> B} =
             ennreal (real (card AT) / 2 ^ n) * emeasure coin_space B"
    unfolding P_def
    apply (subst (1) Suc.IH)
    sorry
  also have "P {x. stake n x \<in> AF \<and> sdrop n x \<in> B} =
             ennreal (real (card AF) / 2 ^ n) * emeasure coin_space B"
    unfolding P_def
    apply (subst (1) Suc.IH)
    sorry
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

    have "emeasure (measure_pmfsr' p) X = emeasure coin_space (run_pmfsr p -` X)"
      unfolding measure_pmfsr'_def using X
      apply (subst emeasure_distr)
        apply (auto simp: space_coin_space)
      sorry
    also have "\<dots> = emeasure coin_space
                      ((\<lambda>bs. map_option (\<lambda>(x, n). (x, sdrop n bs)) (p bs)) -` Some ` ({x} \<times> Y))"
      unfolding run_pmfsr_def X_def ..
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
      apply simp
      by (smt (verit, del_insts) coin_space.emeasure_space_1 mult.right_neutral space_coin_space)
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
    apply (auto simp: run_pmfsr_def fun_eq_iff map_option_case split: option.splits)
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
      apply (auto simp: o_def fun_eq_iff run_pmfsr_def split: option.splits)
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

lemma spmf_of_return_pmfsr:
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

lemma spmf_of_coin_pmfsr:
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


definition ord_pmfsr :: "'a pmfsr \<Rightarrow> 'a pmfsr \<Rightarrow> bool" where
  "ord_pmfsr = rel_fun (=) (ord_option (=))"



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

lemma bind_pmfsr_cong:
  "p = q \<Longrightarrow> (\<And>x. x \<in> range_pmfsr q \<Longrightarrow> f x = g x) \<Longrightarrow> bind_pmfsr p f = bind_pmfsr q g"
  by (auto simp: bind_pmfsr_def fun_eq_iff Option_bind_conv_case in_range_pmfsrI split: option.splits)

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

code_lazy_type stream

partial_function (pmfsr) bernoulli_pmfsr :: "real \<Rightarrow> bool pmfsr" where
  "bernoulli_pmfsr p =
     do {b \<leftarrow> coin_pmfsr;
         if b then
           return_pmfsr (p \<ge> 1/2)
         else
           bernoulli_pmfsr (if p < 1/2 then 2 * p else 2 * p - 1)}"

lemmas [code] = bernoulli_pmfsr.simps

value "bernoulli_pmfsr (1/3) (replicate 3 False @- sconst True)"

(*
definition geometric_pmfsr where
  "geometric_pmfsr = 
*)

partial_function (pmfsr) geometric_pmfsr :: "unit \<Rightarrow> nat pmfsr" where
  "geometric_pmfsr x =
     do {b \<leftarrow> coin_pmfsr;
         if b then return_pmfsr 0 else map_pmfsr Suc (geometric_pmfsr ())}"

lemmas [code] = geometric_pmfsr.simps

value "geometric_pmfsr () (replicate 3 False @- sconst True)"


context
  fixes n :: nat
begin

partial_function (pmfsr) fast_dice_roll :: "nat \<Rightarrow> nat \<Rightarrow> nat pmfsr"
where
  "fast_dice_roll v c = 
  (if v \<ge> n then if c < n then return_pmfsr c else fast_dice_roll (v - n) (c - n)
   else do {
     b \<leftarrow> coin_pmfsr;
     fast_dice_roll (2 * v) (2 * c + (if b then 1 else 0)) } )"

definition fast_uniform :: "nat pmfsr"
  where "fast_uniform = fast_dice_roll 1 0"

end

lemmas [code] = fast_dice_roll.simps

value "fast_uniform 10 ([True, False, True, True, False] @- sconst False)"
value "fast_uniform 10 ([False, False, True, True, False] @- sconst False)"
value "fast_uniform 10 ([True, False, True, False, False] @- sconst False)"
value "fast_uniform 10 ([True, False, True, True, True] @- sconst False)"
value "fast_uniform 10 ([True, False, True, True, False, True, True, False, True] @- sconst False)"
value "fast_uniform 10 ([True, True, True, True, True, True, False, True, True] @- sconst False)"


end