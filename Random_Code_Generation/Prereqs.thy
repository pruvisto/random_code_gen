theory Prereqs
  imports "HOL-Probability.Probability"
begin



definition coin_space :: "bool stream measure" where
  "coin_space = stream_space (measure_pmf (pmf_of_set UNIV))"

lemma space_coin_space: "space coin_space = UNIV"
  by (simp add: coin_space_def space_stream_space)

interpretation coin_space: prob_space coin_space
  unfolding coin_space_def
  by (intro prob_space.prob_space_stream_space prob_space_measure_pmf)

lemma emeasure_coin_space_UNIV [simp]: "emeasure coin_space UNIV = 1"
  using coin_space.emeasure_space_1 space_coin_space by force

lemma prob_coin_space_UNIV [simp]: "coin_space.prob UNIV = 1"
  using coin_space.prob_space space_coin_space by auto

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


end