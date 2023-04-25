theory Prefix_Tree
  imports "HOL-Library.Sublist" "HOL-Library.Stream" "HOL-Library.Monad_Syntax"
begin

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


definition sprefix where "sprefix xs ys \<longleftrightarrow> stake (length xs) ys = xs"

lemma sprefix_altdef: "sprefix xs ys \<longleftrightarrow> (\<exists>zs. ys = xs @- zs)"
  unfolding sprefix_def
  by (metis append.right_neutral cancel_comm_monoid_add_class.diff_cancel order.refl 
            stake_invert_Nil stake_sdrop stake_shift take_all)

lemma sprefixI: "stake (length xs) ys = xs \<Longrightarrow> sprefix xs ys"
  by (auto simp: sprefix_def)

lemma sprefixE:
  assumes "sprefix xs ys"
  obtains zs where "ys = xs @- zs"
  using assms by (auto simp: sprefix_altdef)

lemma sprefix_imp_stake_eq: "sprefix xs ys \<Longrightarrow> n \<le> length xs \<Longrightarrow> stake n ys = take n xs"
  by (auto simp: sprefix_altdef)

lemma sprefix_imp_stake_eq' [dest]: "sprefix xs ys \<Longrightarrow> stake (length xs) ys = xs"
  by (auto simp: sprefix_altdef)

lemma sprefix_stake [simp, intro]: "sprefix (stake n ys) ys"
  by (simp add: sprefix_def)

lemma sprefix_append_same_iff [simp]: "sprefix (xs @ ys) (xs @- zs) \<longleftrightarrow> sprefix ys zs"
  by (auto simp: sprefix_def)

lemma sprefix_shift_same [simp]: "sprefix xs (xs @- ys)"
  by (auto simp: sprefix_altdef)


lemma Option_bind_conv_case: "Option.bind x f = (case x of None \<Rightarrow> None | Some x \<Rightarrow> f x)"
  by (auto split: option.splits)

lemma shift_eq_shift1:
  "length xs \<le> length ys \<Longrightarrow> xs @- xs' = ys @- ys' \<longleftrightarrow>
     (let n = length ys - length xs in ys = xs @ stake n xs' \<and> sdrop n xs' = ys')"
  apply (auto simp: Let_def)
    apply (metis sprefix_altdef sprefix_def stake_shift_big)
   apply (metis Stream.sdrop_shift diff_is_0_eq' drop_eq_Nil2 sdrop.simps(1) shift.simps(1) verit_comp_simplify1(2))
  by (metis shift_append stake_sdrop)

lemma shift_eq_shift2:
  "length xs \<ge> length ys \<Longrightarrow> xs @- xs' = ys @- ys' \<longleftrightarrow>
     (let n = length xs - length ys in xs = ys @ stake n ys' \<and> sdrop n ys' = xs')"
  using shift_eq_shift1[of ys xs] by (auto simp: Let_def eq_commute)

lemma prefix_conv_take: "prefix xs ys \<longleftrightarrow> take (length xs) ys = xs"
  by (metis append_eq_conv_conj prefix_def)

lemma sprefix_shiftD:
  assumes "sprefix xs (ys @- zs)"
  shows   "\<not>parallel xs ys"
  using assms unfolding parallel_def
  by (cases "length xs \<ge> length ys")
     (auto simp: sprefix_def prefix_conv_take append_eq_conv_conj)    

definition the_elem' :: "'a set \<Rightarrow> 'a option" where
  "the_elem' X = (if is_singleton X then Some (the_elem X) else None)"

lemma the_elem'_empty [simp]: "the_elem' {} = None"
  by (auto simp: the_elem'_def is_singleton_def)

lemma the_elem'_singleton [simp]: "the_elem' {x} = Some x"
  by (auto simp: the_elem'_def)

typedef 'a ptree = "{X::'a list set. pairwise parallel X}"
  morphisms set_ptree Abs_ptree
  by (rule exI[of _ "{}"]) auto

setup_lifting type_definition_ptree




instantiation ptree :: (type) order
begin

lift_definition less_eq_ptree :: "'a ptree \<Rightarrow> 'a ptree \<Rightarrow> bool" is
  "(\<subseteq>)" .

lift_definition less_ptree :: "'a ptree \<Rightarrow> 'a ptree \<Rightarrow> bool" is
  "(\<subset>)" .

instance 
  by intro_classes (transfer; force)+

end

lemma less_eq_ptree_altdef: "t \<le> t' \<longleftrightarrow> set_ptree t \<subseteq> set_ptree t'"
  by transfer auto



instantiation ptree :: (type) order_bot
begin

lift_definition bot_ptree :: "'a ptree" is "{}"
  by auto

instance by intro_classes (transfer; force; fail)

end

lemma set_bot_ptree [simp]: "set_ptree bot = {}"
  by transfer auto


definition pairwise' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "pairwise' P A B \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. x \<noteq> y \<longrightarrow> P x y)"

lemma pairwise'I [intro?]: "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> x \<noteq> y \<Longrightarrow> P x y) \<Longrightarrow> pairwise' P A B"
  by (auto simp: pairwise'_def)

lemma pairwise'D: "pairwise' P A B \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> x \<noteq> y \<Longrightarrow> P x y"
  by (auto simp: pairwise'_def)

lemma pairwise'_empty [simp]: "pairwise' P {} B" "pairwise' P A {}"
  by (auto simp: pairwise'_def)

lemma pairwise'_singleton:
  "pairwise' P {x} B \<longleftrightarrow> (\<forall>y\<in>B-{x}. P x y)"
  "pairwise' P A {y} \<longleftrightarrow> (\<forall>x\<in>A-{y}. P x y)"
  by (auto simp: pairwise'_def)

lemma pairwise'_mono: "pairwise' P A B \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> pairwise' P A' B'"
  by (auto simp: pairwise'_def)

lemma set_ptree_eq_iff [simp]: "set_ptree t = set_ptree t' \<longleftrightarrow> t = t'"
  by transfer auto


lift_definition singleton_ptree :: "'a list \<Rightarrow> 'a ptree" is "\<lambda>xs. {xs}"
  by auto

lemma set_singleton_ptree [simp]: "set_ptree (singleton_ptree xs) = {xs}"
  by transfer auto



lift_definition ptree_of_length :: "nat \<Rightarrow> 'a ptree" is "\<lambda>n. {xs. length xs = n}"
  by (auto simp: pairwise_def not_equal_is_parallel parallelD1)

lemma ptree_of_length_0 [simp]: "ptree_of_length 0 = singleton_ptree []"
  by transfer auto

lemma set_ptreeD:
  assumes "xs \<in> set_ptree t" "ys \<in> set_ptree t" "xs \<noteq> ys"
  shows   "xs \<parallel> ys"
  using assms by transfer (auto simp: pairwise_def)

lemma set_ptree_prefixD:
  assumes "xs \<in> set_ptree t" "ys \<in> set_ptree t" "prefix xs ys"
  shows   "xs = ys"
  using assms by transfer (auto simp: pairwise_def)

lemma set_ptree_bot [simp]: "set_ptree bot = {}"
  by transfer auto

lemma set_ptree_of_length [simp]: "set_ptree (ptree_of_length n) = {xs. length xs = n}"
  by transfer auto


definition ptree_compatible :: "'a ptree set \<Rightarrow> bool" where
  "ptree_compatible Y = pairwise (pairwise' parallel) (set_ptree ` Y)"


lemma ptree_chain_imp_compatible:
  assumes "Complete_Partial_Order.chain (\<le>) Y"
  shows   "ptree_compatible Y"
  unfolding ptree_compatible_def
proof (intro pairwiseI pairwise'I; elim imageE; clarify)
  fix t t' :: "'a ptree" and xs ys :: "'a list"
  assume *: "set_ptree t \<noteq> set_ptree t'" "t \<in> Y" "t' \<in> Y"
            "xs \<in> set_ptree t" "ys \<in> set_ptree t'" "xs \<noteq> ys"
  from assms have "t \<le> t' \<or> t' \<le> t"
    using * unfolding chain_def by blast
  thus "xs \<parallel> ys"
    using * set_ptreeD unfolding less_eq_ptree_altdef by blast
qed


instantiation ptree :: (type) Inf
begin

lift_definition Inf_ptree :: "'a ptree set \<Rightarrow> 'a ptree" is
  "\<lambda>X. if X = {} then {} else Inf X"
  by (auto simp: pairwise_def)

instance ..

end

lemma Inf_ptree_lower: "x \<in> X \<Longrightarrow> Inf X \<le> (x :: 'a ptree)"
  by transfer auto

lemma Inf_ptree_greatest: "X \<noteq> {} \<Longrightarrow> (\<And>y. y \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> Inf X \<ge> (x :: 'a ptree)"
  by transfer auto  


instantiation ptree :: (type) Sup
begin

lift_definition Sup_ptree :: "'a ptree set \<Rightarrow> 'a ptree" is 
  "\<lambda>Y. if pairwise (pairwise' parallel) Y then Sup Y else {}"
proof -
  fix Y :: "'a list set set"
  assume Y: "\<And>X. X \<in> Y \<Longrightarrow> pairwise parallel X"
  show "pairwise parallel (if pairwise (pairwise' parallel) Y then \<Union> Y else {})"
  proof (cases "pairwise (pairwise' parallel) Y")
    case True
    have "pairwise parallel (\<Union> Y)"
    proof (intro pairwiseI; safe)
      fix X X' xs ys assume *: "X \<in> Y" "X' \<in> Y" "xs \<in> X" "ys \<in> X'" "xs \<noteq> ys"
      thus "parallel xs ys"
        using Y[of X] Y[of X'] * True unfolding pairwise_def pairwise'_def by metis
    qed
    thus ?thesis
      by simp
  qed auto
qed

instance ..

end


lemma Sup_ptree_upper:
  assumes "ptree_compatible Y" "t \<in> Y"
  shows   "t \<le> Sup Y"
  using assms unfolding ptree_compatible_def by transfer auto

lemma ptree_compatible_altdef:
  "ptree_compatible X \<longleftrightarrow> (\<exists>t. \<forall>t'\<in>X. t' \<le> t)"
  apply auto
  using Sup_ptree_upper apply auto[1]
  unfolding ptree_compatible_def
  apply (auto simp: pairwise_def pairwise'_def less_eq_ptree_altdef intro: set_ptreeD)
  done

lemma Sup_ptree_least:
  assumes "\<And>t'. t' \<in> Y \<Longrightarrow> t' \<le> t"
  shows   "Sup Y \<le> (t :: 'a ptree)"
proof -
  have "ptree_compatible Y"
    unfolding ptree_compatible_altdef using assms by blast
  thus ?thesis
    using assms unfolding ptree_compatible_def by transfer auto
qed

instance ptree :: (type) ccpo
  by intro_classes (use Sup_ptree_upper Sup_ptree_least ptree_chain_imp_compatible in blast)+

lemma Sup_ptree_empty [simp]: "Sup {} = (bot :: 'a ptree)"
  by transfer auto

lemma set_ptree_Sup: "ptree_compatible Y \<Longrightarrow> set_ptree (Sup Y) = (\<Union>t\<in>Y. set_ptree t)"
  unfolding ptree_compatible_def by transfer auto

lemma ptree_compatible_singletons_set_ptree:
  "ptree_compatible (singleton_ptree ` set_ptree t)"
  by (auto simp: ptree_compatible_def pairwise_def pairwise'_def dest: set_ptreeD)

lemma ptree_decompose: "t = (SUP xs\<in>set_ptree t. singleton_ptree xs)"
proof -
  have "set_ptree (SUP xs\<in>set_ptree t. singleton_ptree xs) = set_ptree t"
    using ptree_compatible_singletons_set_ptree[of t] by (subst set_ptree_Sup) auto
  thus ?thesis
    by simp
qed




lift_definition prefix_of_ptree :: "'a ptree \<Rightarrow> 'a stream \<Rightarrow> 'a list option" is
  "\<lambda>X xs. the_elem' {ys\<in>X. sprefix ys xs}" .

lemma prefix_of_ptree_bot [simp]: "prefix_of_ptree bot xs = None"
  by transfer (auto simp: the_elem'_def is_singleton_def)

lemma prefix_of_ptree_eq_NoneI:
  "(\<And>ys. ys \<in> set_ptree t \<Longrightarrow> \<not>sprefix ys xs) \<Longrightarrow> prefix_of_ptree t xs = None"
  by transfer (auto simp: the_elem'_def is_singleton_def)

lemma prefix_of_ptree_eq_SomeI:
  "ys \<in> set_ptree t \<Longrightarrow> sprefix ys xs \<Longrightarrow> prefix_of_ptree t xs = Some ys"
proof (transfer fixing: xs ys)
  fix X :: "'a list set"
  assume X: "pairwise parallel X"
  assume ys: "ys \<in> X" "sprefix ys xs"
  then obtain xs' where [simp]: "xs = ys @- xs'"
    by (auto simp: sprefix_altdef)
  have "{ys\<in>X. sprefix ys xs} = {ys}"
  proof (intro equalityI subsetI)
    fix zs assume "zs \<in> {zs\<in>X. sprefix zs xs}"
    hence zs: "zs \<in> X" "sprefix zs xs"
      by auto
    thus "zs \<in> {ys}"
      using ys pairwiseD[OF X, of ys zs] by (auto dest: sprefix_shiftD)
  qed (use ys in auto)
  thus "the_elem' {ys\<in>X. sprefix ys xs} = Some ys"
    by simp
qed

lemma prefix_of_ptree_eq_None_iff:
  "prefix_of_ptree t xs = None \<longleftrightarrow> (\<forall>ys\<in>set_ptree t. \<not>sprefix ys xs)"
  by (metis option.discI prefix_of_ptree_eq_NoneI prefix_of_ptree_eq_SomeI)

lemma prefix_of_ptree_eq_Some_iff:
  "prefix_of_ptree t xs = Some ys \<longleftrightarrow> ys \<in> set_ptree t \<and> sprefix ys xs"
  by (metis option.distinct(1) option.inject prefix_of_ptree_eq_None_iff prefix_of_ptree_eq_SomeI)

lemmas prefix_of_ptree_simps = prefix_of_ptree_eq_None_iff prefix_of_ptree_eq_Some_iff

lemma prefix_of_ptree_eq_None [simp]:
  "\<not>sprefix xs ys \<Longrightarrow> prefix_of_ptree (singleton_ptree xs) ys = None"
  by (auto simp: prefix_of_ptree_simps)

lemma prefix_of_ptree_eq_Some [simp]:
  "sprefix xs ys \<Longrightarrow> prefix_of_ptree (singleton_ptree xs) ys = Some xs"
  by (auto simp: prefix_of_ptree_simps)

lemma prefix_of_ptree_singleton:
  "prefix_of_ptree (singleton_ptree xs) ys = (if sprefix xs ys then Some xs else None)"
  by auto

lemma prefix_of_ptree_of_length [simp]:
  "prefix_of_ptree (ptree_of_length n) xs = Some (stake n xs)"
  by (auto simp: prefix_of_ptree_simps)

lift_definition bind_ptree :: "'a ptree \<Rightarrow> ('a list \<Rightarrow> 'a ptree) \<Rightarrow> 'a ptree" is
  "\<lambda>X f. \<Union>xs\<in>X. (@) xs ` f xs"
proof -
  fix X :: "'a list set" and f :: "'a list \<Rightarrow> 'a list set"
  assume X: "pairwise parallel X"
  assume f: "\<And>xs. pairwise parallel (f xs)"
  show "pairwise parallel (\<Union>xs\<in>X. (@) xs ` f xs)"
  proof (rule pairwiseI; safe)
    fix xs xs' ys ys' :: "'a list"
    assume *: "xs @ ys \<noteq> xs' @ ys'" "xs \<in> X" "xs' \<in> X" "ys \<in> f xs" "ys' \<in> f xs'"
    show "parallel (xs @ ys) (xs' @ ys')"
    proof (cases "xs = xs'")
      case [simp]: True
      hence "ys \<noteq> ys'"
        using *(1) by auto
      with * f[of xs] have "parallel ys ys'"
        using pairwiseD by fastforce
      thus ?thesis
        by (auto simp: parallel_def)
    next
      case False
      with * X have "parallel xs xs'"
        using pairwiseD by metis
      thus ?thesis
        by (auto intro: parallel_append)
    qed
  qed
qed

lemma set_ptree_bind:
  "set_ptree (bind_ptree t f) = (\<Union>xs\<in>set_ptree t. (@) xs ` set_ptree (f xs))"
  by transfer auto

lemma bind_ptree_mono: 
  "t \<le> t' \<Longrightarrow> (\<And>x. x \<in> set_ptree t \<Longrightarrow> f x \<le> f' x) \<Longrightarrow> bind_ptree t f \<le> bind_ptree t' f'"
  by transfer fast

lemma prefix_of_ptree_bind:
  "prefix_of_ptree (bind_ptree t f) xs =
     do {ys \<leftarrow> prefix_of_ptree t xs;
         zs \<leftarrow> prefix_of_ptree (f ys) (sdrop (length ys) xs);
         Some (ys @ zs)}"
proof (cases "prefix_of_ptree t xs")
  case None
  hence *: "\<not>sprefix ys xs" if "ys \<in> set_ptree t" for ys
    using that by (auto simp: prefix_of_ptree_eq_None_iff)
  have "prefix_of_ptree (bind_ptree t f) xs = None"
  proof (rule prefix_of_ptree_eq_NoneI)
    fix ts assume "ts \<in> set_ptree (bind_ptree t f)"
    then obtain ys zs where ts: "ys \<in> set_ptree t" "zs \<in> set_ptree (f ys)" "ts = ys @ zs"
      by (auto simp: set_ptree_bind)
    have "\<not>sprefix ys xs"
      by (rule *) fact
    thus "\<not>sprefix ts xs"
      by (auto simp: ts sprefix_altdef)
  qed
  thus ?thesis
    using None by simp
next
  case (Some ys)
  hence ys: "ys \<in> set_ptree t" and "sprefix ys xs"
    by (auto simp: prefix_of_ptree_eq_Some_iff)
  then obtain xs' where [simp]: "xs = ys @- xs'"
    by (auto simp: sprefix_altdef)
  have [simp]: "prefix_of_ptree t (ys @- xs') = Some ys"
    using Some \<open>xs = ys @- xs'\<close> by metis

  show ?thesis
  proof (cases "prefix_of_ptree (f ys) xs'")
    case None
    hence *: "\<not>sprefix zs xs'" if "zs \<in> set_ptree (f ys)" for zs
      using that by (simp add: prefix_of_ptree_eq_None_iff)

    have "prefix_of_ptree (bind_ptree t f) (ys @- xs') = None"
    proof (rule prefix_of_ptree_eq_NoneI)
      fix ts assume "ts \<in> set_ptree (bind_ptree t f)"
      then obtain ys' zs where ts: "ys' \<in> set_ptree t" "zs \<in> set_ptree (f ys')" "ts = ys' @ zs"
        by (auto simp: set_ptree_bind)
      show "\<not>sprefix ts (ys @- xs')"
        using * parallel_append same_prefix_prefix set_ptreeD ts ys
        by (metis shift_append shift_left_inj sprefix_altdef sprefix_shiftD)
    qed
    thus ?thesis
      using ys by (simp add: None)
  next
    case (Some zs)
    hence zs: "zs \<in> set_ptree (f ys)" and "sprefix zs xs'"
      by (auto simp: prefix_of_ptree_eq_Some_iff)
    then obtain xs'' where [simp]: "xs' = zs @- xs''"
      by (auto simp: sprefix_altdef)
    have [simp]: "prefix_of_ptree t (ys @- zs @- xs'') = Some ys"
                 "prefix_of_ptree (f ys) (zs @- xs'') = Some zs"
      using Some \<open>xs' = zs @- xs''\<close> \<open>xs = ys @- xs'\<close> \<open>prefix_of_ptree t (ys @- xs') = _\<close>
      by metis+
    have "prefix_of_ptree (bind_ptree t f) (ys @- zs @- xs'') = Some (ys @ zs)"
      using ys zs by (intro prefix_of_ptree_eq_SomeI) (auto simp: set_ptree_bind)
    thus ?thesis
      by simp
  qed
qed

end