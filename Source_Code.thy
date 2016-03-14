theory Source_Code
imports "~~/src/HOL/Probability/Information"
begin
(*
AIM: Formalize Shannon's theorems
*)

section{* Basic types *}

type_synonym bit = bool
type_synonym bword = "bit list"
type_synonym letter = nat
type_synonym 'b word = "'b list"

type_synonym 'b encoder = "'b word \<Rightarrow> bword"
type_synonym 'b decoder = "bword \<Rightarrow> 'b word option"
type_synonym 'b code = "'b encoder * 'b decoder"

type_synonym 'b prob = "'b \<Rightarrow> real"

section{* First locale, generic to both Shannon's theorems *}
(*
X is the input, Y is the output.
They are not independent (if they are, all of this serves no purpose)
We fix N, N' the measures (TODO: should I? Can we have two different bit measures?)
The input is only correlated to the corresponding output.
From a code, we consider:
_its extension: the code obtained when we encode each
letter and concatenate the result (and fortunately decode it if it has some good
properties).
_its block code, with a natural parameter, that takes mentioned number of
letters, consider it as a single character (of a new alphabet), and encode it.
*)

(* locale generic to both theorems *)
locale source_code = information_space +
(* information source *)
  fixes fi :: "'b \<Rightarrow> real"
  fixes X::"'a \<Rightarrow> 'b"
  assumes distr_i: "simple_distributed M X fi"
(*
According to RAHM, this should be a rat: my impression is that they aim for a code that can achieve
precisely this rate, however the gist is that we can achieve a rate equal OR better than H + \<epsilon>, so
in my mind it is not that important. In the Shannon's original paper it is not clear to me either.
*)
  fixes H::real

(*
The entropy depends on the value of b, which is the cardinal of the set of available
output symbols.
*)
(*
I have tried to use statements that do not use the value of b explicitly, using b_gt_1 whenever
possible. However it is not possible to avoid using this value altogether, since it is encoded in
the output type of the code (which is a bword, a word of bits). This is one of the shortcomings of
Isabelle vs Coq/SSreflect, where dependent parameter types are available.
*)
  assumes b_val: "b = 2"
  assumes entropy_defi: "H = \<H>(X)"

  fixes L :: "'b set"
  assumes fin_L: "finite L"
  assumes emp_L: "L \<noteq> {}"

(*
TLDR: technicality
The assumption boils down to say that for all letter l in L, there is a "omega" such that X(omega) =
l. Even with that, we can still have P(X=l) = 0, if only by modifying X for one value in the
(continuous) probability space but keeping the same distribution.
*)
  assumes bounded_input: "X ` space M = L"

  fixes c::"'b code"
  assumes real_code : "((\<forall>x. snd c (fst c x) = Some x) \<and>
(\<forall>w. (fst c) w = [] \<longleftrightarrow> w = []) \<and>
(\<forall>x. x \<noteq> [] \<longrightarrow> fst c x = (fst c) [(hd x)] @ (fst c) (tl x)))"

(*
TODO: Have some predicates to allow reasonings about codes. Keep the input_block_size that limits
the size of the input, and use it.
*)
(*
We will generalize the type "code" to any input by splitting the input in piece of length below a
constant.
*)
section{* Source coding theorem, direct: the entropy is a lower bound *}
context source_code
begin
subsection{* Codes and words *}

abbreviation real_word :: "'b word \<Rightarrow> bool" where
  "real_word w \<equiv> (set w \<subseteq> L)"


abbreviation k_words :: "nat \<Rightarrow> ('b word) set" where
  "k_words k \<equiv> {w. length w = k \<and> real_word w}"

lemma rw_tail: "real_word w \<Longrightarrow> w = [] \<or> real_word (tl w)"
    by (metis dual_order.trans list.collapse set_subset_Cons)

(*
length of the codeword associated with the letter
*)
definition code_word_length :: "'e code \<Rightarrow> 'e \<Rightarrow> nat" where
  "code_word_length co l = length ((fst co) [l])"

abbreviation cw_len :: "'b \<Rightarrow> nat" where
  "cw_len l \<equiv> code_word_length c l"

(*
The code rate is the expectation of the length of the code taken on all inputs (which is a finite
set, the set of letters).
*)
definition code_rate :: "'e code \<Rightarrow> ('a \<Rightarrow> 'e) \<Rightarrow> real" where
  "code_rate co Xo = expectation (\<lambda>a. (code_word_length co ((Xo) a)))"

definition cr :: "real" where
  "cr = expectation (\<lambda>a. (cw_len ((X) a)))"

lemma fi_pos: "i\<in> L \<Longrightarrow> 0 \<le> fi i"
    using simple_distributed_nonneg[OF distr_i] bounded_input by auto

(*
Proof by Johannes Hölzl
*)
lemma (in prob_space) simp_exp_composed:
  assumes X: "simple_distributed M X Px"
shows "expectation (\<lambda>a. f (X a)) = (\<Sum>x \<in> X`space M. f x * Px x)"
    using distributed_integral[OF simple_distributed[OF X], of f]
    by (simp add: lebesgue_integral_count_space_finite[OF simple_distributed_finite[OF X]] ac_simps)

lemma cr_rw:
  "cr = (\<Sum>i \<in> X ` space M. fi i * cw_len i)" unfolding cr_def
    using simp_exp_composed[OF distr_i, of "cw_len"]
    by (simp add:mult.commute)

abbreviation cw_len_concat :: "'b word \<Rightarrow> nat" where
  "cw_len_concat w \<equiv> foldr (\<lambda>x s. (cw_len x) + s) w 0"

lemma cw_len_length: "cw_len_concat w = length (fst c w)"
proof (induction w)
    case Nil
    show ?case using real_code by simp
    case (Cons a w)
    have "cw_len_concat (a # w) = cw_len a + cw_len_concat w" by simp
    thus ?case using code_word_length_def real_code Cons
      by (metis length_append list.distinct(1) list.sel(1) list.sel(3))
qed

lemma maj_fold:
  fixes f::"'b \<Rightarrow> nat"
  assumes bounded: "\<And>l. l\<in>L \<Longrightarrow> f l \<le> bound"
shows "real_word w \<Longrightarrow> foldr (\<lambda>x s. f x + s) w 0 \<le> length w * bound"
proof (induction w)
    case Nil
    thus ?case by simp
next
    case (Cons x xs)
    assume "real_word (x#xs)"
    moreover hence "real_word xs" by simp
    moreover have "foldr (\<lambda>x s. f x + s) (x#xs) 0 = foldr (\<lambda>x s. f x + s) (xs) 0 + f x" by simp
    ultimately show ?case using assms Cons.IH by fastforce
qed

definition max_len :: "nat" where
  "max_len = Max ((\<lambda>x. cw_len x) ` L)"

lemma max_cw:
  "\<And>l. l \<in> L \<Longrightarrow> cw_len l \<le> max_len"
    by (simp add: max_len_def fin_L)


subsection{* Related to the Kraft theorem *}
definition kraft_sum :: "real" where
  "kraft_sum = (\<Sum>i\<in>L. 1 / b ^ (cw_len i))"

lemma pos_cw_len: "0 < 1 / b ^ cw_len i" using b_gt_1 by simp

lemma kraft_sum_nonnull: "0 < kraft_sum"
    using emp_L fin_L pos_cw_len setsum_pos kraft_sum_def
    by metis

lemma kraft_sum_powr: "kraft_sum = (\<Sum>i\<in>L. 1 / b powr (cw_len i))"
    using powr_realpow b_gt_1
    by (simp add: kraft_sum_def)

definition kraft_inequality :: "bool" where
  "kraft_inequality = (kraft_sum \<le> 1)"

lemma k_words_rel:
  "\<And>k. k_words (Suc k) = {w. (hd w \<in> L \<and> tl w \<in> k_words k \<and> w \<noteq> [])}"
proof
    fix k
    show "k_words (Suc k) \<subseteq> {w. (hd w \<in> L \<and> tl w \<in> k_words k \<and> w \<noteq> [] )}" (is "?l \<subseteq> ?r")
  proof
      fix w
      assume w_kw: "w \<in> k_words (Suc k)"
      hence "real_word w" by simp
      hence "hd w \<in> L"
        by (metis (mono_tags) w_kw hd_in_set list.size(3) mem_Collect_eq nat.distinct(1) subset_code(1))
      moreover have "length w = Suc k" using w_kw by simp
      moreover hence "w \<noteq> []" by auto
      moreover have "real_word (tl w)" using \<open>real_word w\<close> calculation(3) rw_tail by auto
      ultimately show "w \<in> ?r" using w_kw by simp
  qed
next
    fix k
    show "k_words (Suc k) \<supseteq> {w. (hd w \<in> L \<and> tl w \<in> k_words k \<and> w \<noteq> [])}"
  proof
      fix w
      assume asm: "w \<in> {w. hd w \<in> L \<and> tl w \<in> {w. length w = k \<and> real_word w} \<and> w \<noteq>
      []}"
      hence " hd w \<in> L \<and> length (tl w) = k \<and> real_word (tl w)" by simp
      hence "real_word w"
        by (metis empty_iff insert_subset list.collapse list.set(1) set_simps(2) subsetI)
      moreover hence "length w = Suc k" using asm by auto
      ultimately show "w \<in> k_words (Suc k)" by simp
  qed
qed

lemma bij_k_words:
shows "\<And>k. bij_betw (\<lambda>wi. Cons (fst wi) (snd wi)) (L \<times> (k_words k)) (k_words (Suc k))"
    unfolding bij_betw_def
proof
    fix k
    let ?f = "(\<lambda>wi. Cons (fst wi) (snd wi))"
    let ?S = "L \<times> (k_words k)"
    let ?T = "k_words (Suc k)"
    show "inj_on ?f ?S" by (simp add: inj_on_def)
    show "?f`?S = ?T"
  proof (rule ccontr)
      assume "?f ` ?S \<noteq> ?T"
      hence "\<exists>w. w\<in> ?T \<and> w \<notin> ?f`?S" by auto
      then obtain w where asm: "w\<in> ?T \<and> w \<notin> ?f`?S" by blast
      hence "w = ?f ((hd w),(tl w))" using k_words_rel by simp
      moreover have "((hd w),(tl w)) \<in> ?S" using k_words_rel asm by simp
      ultimately have "w \<in> ?f`?S" by blast
      thus "False" using asm by simp
  qed
qed

lemma finite_k_words: "finite (k_words k)"
proof (induct k)
    case 0
    show ?case by simp
    case (Suc n)
    thus ?case using bij_k_words bij_betw_finite fin_L by blast
qed

lemma cartesian_product:
  fixes f::"('c \<Rightarrow> real)"
  fixes g::"('d \<Rightarrow> real)"
shows "finite A \<Longrightarrow> finite B \<Longrightarrow>
(\<Sum>b\<in>B. g b)* (\<Sum>a\<in>A. f a) = (\<Sum>ab\<in>A\<times>B. f (fst ab) * g (snd ab))"
    using bilinear_times bilinear_setsum[where h="(\<lambda>x y. x * y)" and f="f" and g="g"]
    by (metis (erased, lifting) setsum.cong split_beta' Groups.ab_semigroup_mult_class.mult.commute)

lemma kraft_sum_power :
shows "kraft_sum ^k = (\<Sum>w \<in> (k_words k). 1 / b^(cw_len_concat w))"
proof (induct k)
    case 0
    have "k_words 0 = {[]}" by auto
    thus ?case by simp
next
    case (Suc n)
    have "kraft_sum ^Suc n = kraft_sum ^n * kraft_sum " by simp
    also have "\<dots> =
  (\<Sum>w \<in> k_words n. 1 / b^cw_len_concat w) * (\<Sum>i\<in>L. 1 / b^cw_len i)"
      using Suc.hyps kraft_sum_def by auto
    also have
    "\<dots> =
  (\<Sum>wi \<in> L \<times> k_words n. 1/b^cw_len (fst wi) * (1 / b^cw_len_concat (snd wi)))"
      using fin_L finite_k_words cartesian_product
      by blast
    also have "\<dots> =
  (\<Sum>wi \<in> L \<times> k_words n. 1 / b^(cw_len_concat (snd wi) + cw_len (fst wi)))"
      by (metis (no_types, lifting) power_add add.commute power_one_over)
    also have "\<dots> =
  (\<Sum>wi \<in> L \<times> k_words n. 1 / b^cw_len_concat (fst wi # snd wi))"
      by (metis (erased, lifting) add.commute comp_apply foldr.simps(2))
    also have "\<dots> = (\<Sum>w \<in> (k_words (Suc n)). 1 / b^(cw_len_concat w))"
      using bij_k_words setsum.reindex_bij_betw by fastforce
    finally show ?case by simp
qed

lemma bound_len_concat:
shows "\<And>w. w \<in> k_words k \<Longrightarrow> cw_len_concat w \<le> k * max_len"
    using max_cw maj_fold by blast

subsection{* Inequality of the kraft sum (source coding theorem, direct) *}
subsubsection{* Sum manipulation lemmas and McMillan theorem *}

lemma real_plus_one:
shows "real ((n::nat) + 1) * r = (n * r + r)"
    by (simp add: semiring_normalization_rules(2))

lemma sum_vimage_proof:
  fixes g::"nat \<Rightarrow> real"
  assumes "\<And>w. f w < bd"
shows "finite S \<Longrightarrow> (\<Sum>w\<in>S. g (f w)) = (\<Sum> m=0..<bd. (card ((f-`{m}) \<inter> S) )* g m)"
(is "_ \<Longrightarrow> _ = (\<Sum> m=0..<bd. ?ff m S)")
proof (induct S rule: finite_induct)
    case empty
    show ?case by simp
next
    case (insert x F)
    let ?rr = "(\<Sum>m = 0..<bd. ?ff m (insert x F))"
  (* focusing of the right hand term *)
    have "(f x) \<in> {0..<bd}" using assms by simp
    hence "\<And>h::(nat \<Rightarrow> real). (\<Sum>m=0..<bd. h m) = (\<Sum>y\<in>({0..<bd} - {f x}).h y) + h (f x)"
      by (metis diff_add_cancel finite_atLeastLessThan setsum_diff1_ring)
    moreover hence
    "(\<Sum>m = 0..<bd. ?ff m (insert x F))
    = (\<Sum>m\<in>{0..<bd} - {f x}. ?ff m (insert x F)) + card (f -` {f x} \<inter> F) * g (f x) + g (f x)"
      using insert real_plus_one by fastforce
    ultimately have "(\<Sum>m = 0..<bd. ?ff m (insert x F)) = (\<Sum>m\<in>{0..<bd}. ?ff m F) + g (f x)"
      by fastforce
    thus ?case using insert by simp
qed


lemma sum_vimage:
  fixes g::"nat \<Rightarrow> real"
  assumes bounded: "\<And>w. w \<in> S \<Longrightarrow> f w < bd" and "0 < bd"
shows "finite S \<Longrightarrow> (\<Sum>w\<in>S. g (f w)) = (\<Sum> m=0..<bd. (card ((f-`{m}) \<inter> S) ) * g m)"
(is "?fin \<Longrightarrow> ?s1 = ?s2")
proof -
    let ?ff = "(\<lambda>x. if x\<in>S then f x else 0)"
    let ?ss1 = "(\<Sum>w\<in>S. g (?ff w))"
    let ?ss2 = "(\<Sum> m=0..<bd. (card ((?ff-`{m}) \<inter> S) ) * g m)"
    have "?s1 =?ss1" by simp
    moreover have"\<And>m. ?ff -`{m} \<inter> S = f-`{m} \<inter> S" by auto
    moreover hence "?s2 = ?ss2" by simp
    moreover have "\<And>w . ?ff w < bd" using assms by simp
    moreover hence "?fin \<Longrightarrow> ?ss1 = ?ss2"
      using sum_vimage_proof[of "?ff"] by blast
    ultimately show "?fin \<Longrightarrow> ?s1 = ?s2" by metis
qed



(*
5.54
*)
lemma kraft_sum_rewrite :
  "(\<Sum>w \<in> (k_words k). 1 / b^(cw_len_concat w)) = (\<Sum>m=0..<Suc (k*max_len). card (k_words k \<inter>
((cw_len_concat) -` {m})) * (1 / b^m))" (is "?L = ?R")
proof -
    have "\<And>w. w \<in> k_words k \<Longrightarrow> cw_len_concat w < Suc ( k * max_len)"
      by (simp add: bound_len_concat le_imp_less_Suc)
    moreover have
    "?R = (\<Sum>m = 0..<Suc (k * max_len).
  (card (cw_len_concat -` {m} \<inter> k_words k)) * (1 / b ^ m))"
      by (metis Int_commute)
    moreover have "0 < Suc (k*max_len)" by simp
    ultimately show ?thesis
      using finite_k_words
    sum_vimage[where f="cw_len_concat" and g = "\<lambda>i. 1/ (b^i)"]
      by fastforce
qed

definition set_of_k_words_length_m :: "nat \<Rightarrow> nat \<Rightarrow> 'b word set" where
  "set_of_k_words_length_m k m = {xk. xk \<in> k_words k} \<inter> (cw_len_concat)-`{m}"

lemma am_inj_code :
shows "inj_on (fst c) ((cw_len_concat)-`{m})" (is "inj_on ?enc ?s")
proof -
    fix x y
    let ?dec = "snd c"
    have "x \<in> ?s \<and> y \<in> ?s \<and> ?enc x = ?enc y \<longrightarrow> ?dec (?enc x) = ?dec (?enc y)" by auto
    moreover have "(\<forall>x. snd c (fst c x) = Some x)" using real_code by blast
    ultimately show ?thesis using inj_on_def[of "?enc" "?s"] by (metis option.inject)
qed

lemma img_inc:
shows "(fst c)`(cw_len_concat)-`{m} \<subseteq> {bl. length bl = m}"
proof
    fix y
    assume "y \<in>(fst c)`(cw_len_concat)-`{m}"
    then obtain x where y_def: "y = fst c x" "x\<in>(cw_len_concat)-`{m}" by auto
    hence "cw_len_concat x = m" by simp
    hence "length (fst c x) = m" using cw_len_length by simp
    thus "y \<in> {bl. length bl = m}" using y_def by simp
qed

lemma bool_list_fin:
  "finite {bl::(bool list). length bl = m}"
proof -
    fix m
    have "{bl. set bl \<subseteq> {True, False} \<and> length bl = m} = {bl. length bl= m}" by auto
    moreover have "finite {bl. set bl \<subseteq> {True, False} \<and> length bl = m}"
      by (simp add: finite_lists_length_eq)
    ultimately show "finite {bl::(bool list). length bl = m}" by simp
qed

lemma bool_lists_card:
shows "card {bl::(bool list). length bl = m} = b^m"
proof -
    fix m
    have "card {b. set b \<subseteq> {True,False} \<and> length b = m} = card {True,False}^m"
      using card_lists_length_eq[of "{True,False}"] by simp
    moreover have "card {True, False} = b" using b_val by simp
    moreover have "\<And>d. d \<in> {c::(bool list). True} \<longleftrightarrow> set d \<subseteq> {True, False}" by auto
    ultimately show "card {b::(bool list). length b = m} = b^m" by simp
qed

lemma img_card:
  assumes "real_code c"
shows "card (fst c`cw_len_concat-`{m}) \<le> b^m"
proof -
    have "card ((fst c)` (cw_len_concat)-`{m}) \<le> card {b::(bool list). length b = m}"
  proof -
      fix m
      show "card ((fst c)` (cw_len_concat)-`{m}) \<le> card {b::(bool list). length b = m}"
        by (metis (mono_tags) bool_list_fin img_inc card_mono)
  qed
    thus ?thesis by (metis bool_lists_card of_nat_le_iff)
qed

lemma am_maj_aux2:
shows "finite ((cw_len_concat)-`{m}) \<and> (card ((cw_len_concat)-`{m})) \<le> b^m"
    by (metis (no_types, lifting) am_inj_code bool_list_fin bool_lists_card card.infinite card_0_eq
  card_image card_mono empty_iff finite_subset img_inc inf_img_fin_dom of_nat_le_iff)

lemma am_maj:
shows "card (set_of_k_words_length_m k m)\<le> b^m" (is "?c \<le> ?b")
proof -
    have "set_of_k_words_length_m k m \<subseteq> (cw_len_concat)-`{m}"
      using set_of_k_words_length_m_def by simp
    hence "card (set_of_k_words_length_m k m) \<le> card ((cw_len_concat)-`{m})"
      using assms am_maj_aux2 card_mono by blast
    thus ?thesis using real_code am_maj_aux2[of m] by simp
qed

lemma empty_set_k_words:
  assumes "0 < k"
shows "set_of_k_words_length_m k 0 = {}"
proof (rule ccontr)
    assume "\<not> set_of_k_words_length_m k 0 = {}"
    hence "\<exists>x. x \<in> set_of_k_words_length_m k 0" by auto
    then obtain x where x_def: "x \<in> set_of_k_words_length_m k 0" by auto
    hence "x \<noteq> []" unfolding set_of_k_words_length_m_def using assms by auto
    moreover have "cw_len_concat (hd x#tl x) = cw_len_concat (tl x) + cw_len (hd x)"
      by (metis add.commute comp_apply foldr.simps(2))
    moreover have "(fst c) [(hd x)] \<noteq> []" using assms real_code by blast
    moreover hence "0 < cw_len (hd x)" unfolding code_word_length_def by simp
    ultimately have "x \<notin> set_of_k_words_length_m k 0" by (simp add:set_of_k_words_length_m_def)
    thus "False" using x_def by simp
qed


lemma kraft_sum_rewrite2:
  assumes "0 < k"
shows "(\<Sum>m=0..<Suc (k*max_len). (card (set_of_k_words_length_m k m))/ b^m) \<le> (k * max_len)"
proof -
    have
    "(\<Sum>m=1..<Suc (k*max_len). (card (set_of_k_words_length_m k m) / b^m))
    \<le> (\<Sum>m=1..<Suc(k * max_len). b^m / b^m)"
      using am_maj b_val
    Groups_Big.setsum_mono[of "{1..<Suc(k*max_len)}"
    "(\<lambda>m. (card (set_of_k_words_length_m k m))/b^m)" "\<lambda>m. b^m /b^m"]
      by simp
    moreover have"(\<Sum>m=1..<Suc(k * max_len). b^m / b^m) = (\<Sum>m=1..<Suc(k *max_len). 1)"
      using b_gt_1 by simp
    moreover have "(\<Sum>m=1..<Suc(k*max_len). 1) =(k * max_len)"
      by simp
    ultimately have
    "(\<Sum>m = 1..<Suc (k * max_len). (card (set_of_k_words_length_m k m)) / b ^ m) \<le>(k * max_len)"
      by (metis One_nat_def card_atLeastLessThan card_eq_setsum diff_Suc_Suc real_of_card)
    thus ?thesis using empty_set_k_words assms
      by (simp add: setsum_shift_lb_Suc0_0_upt split: split_if_asm)
qed

lemma kraft_sum_power_bound :
  assumes "0 < k"
shows "kraft_sum^k \<le> (k * max_len)"
    using assms kraft_sum_power kraft_sum_rewrite kraft_sum_rewrite2
    by (simp add: set_of_k_words_length_m_def)

theorem McMillan :
shows "kraft_inequality"
proof -
    have ineq: "\<And>k. 0 < k \<Longrightarrow> (kraft_sum) \<le> root k k * root k (max_len)"
      using kraft_sum_nonnull kraft_sum_power_bound
      by (metis (no_types, hide_lams) not_less of_nat_0_le_iff of_nat_mult power_strict_mono real_root_mult real_root_pos_pos_le real_root_pos_unique real_root_power)
    hence "0 < max_len \<Longrightarrow> (\<lambda>k. root k k * root k (max_len)) \<longlonglongrightarrow> 1"
      using LIMSEQ_root LIMSEQ_root_const tendsto_mult
      by fastforce
    moreover have "\<forall>n\<ge>1. kraft_sum \<le> root n n * root n (max_len)"
      using ineq by simp
    moreover have "max_len = 0 \<Longrightarrow> kraft_sum \<le> 1" using ineq by fastforce
    ultimately have "kraft_sum \<le> 1" using LIMSEQ_le_const by blast
    thus "kraft_inequality" unfolding kraft_inequality_def by simp
qed

lemma entropy_rewrite: "H = -(\<Sum>i \<in> L. fi i * log b (fi i))"
    using entropy_simple_distributed[OF distr_i] bounded_input
    by (simp add: entropy_defi)

lemma log_mult_ext_not_0:
  "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> 0 < z \<Longrightarrow> x * log b (x*z*y) = x * log b (x*z) + x * log b y"
    using b_gt_1 distrib_left log_mult by simp

lemma log_mult_ext_3:
  " 0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> 0 < z \<Longrightarrow> x * log b (x*z*y) = x * log b (x*z) + x * log b y"
    using log_mult_ext_not_0[of x] mult_zero_left[of "log b (0 * z * y)"] by fastforce

lemma log_mult_ext2: "0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> x * log b (x*y) = x * log b (x) + x * log b y"
    by (metis (no_types) log_mult_ext_3 mult.right_neutral zero_less_one)

subsubsection {* KL divergence and properties *}
(*
TODO (eventually): I use a custom definition of the KL_divergence, as it is far simpler for me to
use. It'd be better if in the end I can use the real def definition KL_cus.
*)
definition KL_cus ::"'b set \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> real" where
  "KL_cus S a d = (\<Sum> i \<in> S. a i * log b (a i / d i))"

lemma KL_cus_mul:
  assumes "0 < d" "d \<le> 1"
  assumes "\<And>i. i\<in>S \<Longrightarrow> 0 \<le> a i" "\<And>i. i\<in>S \<Longrightarrow> 0 < e i"
shows "KL_cus S a e \<ge> KL_cus S a (\<lambda>i. e i / d)"
    unfolding KL_cus_def
proof -
    {
    fix i
    assume "i\<in>S"
    hence "(a i / ((e i) / d)) \<le> (a i / e i)" using assms
      by (metis (no_types) divide_1 frac_le less_imp_triv not_less)
    hence "log b (a i / (e i / d)) \<le> log b (a i / e i)" using assms(1)
      by (metis (full_types) b_gt_1 divide_divide_eq_left inverse_divide le_less_linear log_le
    log_neg_const order_refl times_divide_eq_right zero_less_mult_iff)
    }
    hence "\<And>i. i\<in>S \<Longrightarrow> log b (a i / (e i / d)) \<le> log b (a i / e i)" by simp
    thus "(\<Sum>i\<in>S. a i * log b (a i / (e i / d))) \<le> (\<Sum>i\<in>S. a i * log b (a i / e i))"
      by (meson mult_left_mono assms setsum_mono)
qed

lemma KL_cus_pos:
  fixes a e::"'b \<Rightarrow> real"
  assumes fin: "finite S"
  assumes nemp: "S \<noteq> {}"
  assumes non_null: "\<And>i. i\<in>S \<Longrightarrow> 0 < a i" "\<And>i. i\<in> S \<Longrightarrow> 0 < e i"
  assumes sum_a_one: "(\<Sum> i \<in> S. a i) = 1"
  assumes sum_c_one: "(\<Sum> i \<in> S. e i) = 1"
shows "0 \<le> KL_cus S a e"
    unfolding KL_cus_def
proof -
    let ?f = "\<lambda>i. e i / a i"
    have f_pos: "\<And>i. i\<in>S \<Longrightarrow> 0 < ?f i"
      using non_null
      by simp
    have a_pos: "\<And>i. i\<in> S \<Longrightarrow> 0 \<le> a i"
      using non_null
      by (simp add: order.strict_implies_order)
    have "- log b (\<Sum>i\<in>S. a i * e i / a i) \<le> (\<Sum>i\<in>S. a i * - log b (e i / a i))"
      using convex_on_setsum[
    OF fin,
    OF nemp,OF minus_log_convex[OF b_gt_1],
    OF convex_real_interval(3)[of 0],
    OF sum_a_one,
    OF a_pos
    ]
    f_pos
      by fastforce
    also have "- log b (\<Sum>i\<in>S. a i * e i / a i) = -log b (\<Sum>i\<in>S. e i)"
  proof -
      from non_null(1) have "\<And>i. i \<in> S \<Longrightarrow> a i * e i / a i = e i"
        by force
      thus ?thesis
        by simp
  qed
    finally have "0 \<le> (\<Sum>i\<in>S. a i * - log b (e i / a i))"
      using sum_c_one
      by simp
    thus "0 \<le> (\<Sum>i\<in>S. a i * log b (a i / e i))"
      using b_gt_1 log_divide non_null
      by simp
qed

lemma KL_cus_pos_emp:
  "0 \<le> KL_cus {} a e" unfolding KL_cus_def by simp

lemma KL_cus_pos_gen:
  fixes a d::"'b \<Rightarrow> real"
  assumes fin: "finite S"
  assumes non_null: "\<And>i. i\<in>S \<Longrightarrow> 0 < a i" "\<And>i. i\<in> S \<Longrightarrow> 0 < d i"
  assumes sum_a_one: "(\<Sum> i \<in> S. a i) = 1"
  assumes sum_d_one: "(\<Sum> i \<in> S. d i) = 1"
shows "0 \<le> KL_cus S a d"
    using KL_cus_pos KL_cus_pos_emp assms by metis

theorem KL_cus_pos2:
  fixes a d::"'b \<Rightarrow> real"
  assumes fin: "finite S"
  assumes non_null: "\<And>i. i\<in>S \<Longrightarrow> 0 \<le> a i" "\<And>i. i\<in> S \<Longrightarrow> 0 < d i"
  assumes sum_a_one: "(\<Sum> i \<in> S. a i) = 1"
  assumes sum_c_one: "(\<Sum> i \<in> S. d i) = 1"
shows "0 \<le> KL_cus S a d"
proof -
    have "S = (S \<inter> {i. 0 < a i}) \<union> (S \<inter> {i. 0 = a i})" using non_null(1)
      by fastforce
    moreover have "(S \<inter> {i. 0 < a i}) \<inter> (S \<inter> {i. 0 = a i}) = {}" by auto
    ultimately have
    eq: "KL_cus S a d = KL_cus (S \<inter> {i. 0 < a i}) a d + KL_cus (S \<inter> {i. 0 = a i}) a d"
      unfolding KL_cus_def
      by (metis (mono_tags, lifting) fin finite_Un setsum.union_disjoint)
    have "KL_cus (S \<inter> {i. 0 = a i}) a d = 0" unfolding KL_cus_def by simp
    hence "KL_cus S a d = KL_cus (S \<inter> {i. 0 < a i}) a d" using eq by simp
    moreover have "0 \<le> KL_cus (S \<inter> {i. 0 < a i}) a d"
  proof(cases "(S \<inter> {i. 0 < a i}) = {}")
      case True
      thus ?thesis unfolding KL_cus_def by simp
  next
      case False
      let ?c = "\<lambda>i. d i / (\<Sum>j \<in>(S \<inter> {i. 0 < a i}). d j)"
    (* a pos *)
      have 1: "(\<And>i. i \<in> S \<inter> {i. 0 < a i} \<Longrightarrow> 0 < a i)" by simp
    (* ?c pos *)
      have 2: "(\<And>i. i \<in> S \<inter> {i. 0 < a i} \<Longrightarrow> 0 < ?c i)"
        by (metis False IntD1 divide_pos_pos fin finite_Int non_null(2) setsum_pos)
    (* sum a equals to 1 *)
      have 3: "setsum a (S \<inter> {i. 0 < a i}) = 1"
        using setsum.cong[of S, of S, of "(\<lambda>x. if x \<in> {i. 0 < a i} then a x else 0)", of a]
      setsum.inter_restrict[OF fin, of a] non_null(1) sum_a_one
        by fastforce
      have "(\<Sum>i\<in>S \<inter> {j. 0 < a j}. ?c i) = (\<Sum>i\<in>S \<inter> {j. 0 < a j}. d i) / (\<Sum>i\<in>S \<inter> {j. 0 < a j}. d i)"
        by (metis setsum_divide_distrib)
    (* sum ?c equals to 1 *)
      hence 5: "(\<Sum>i\<in>S \<inter> {j. 0 < a j}. ?c i) = 1"
        using 2 False by force
      hence "0 \<le> KL_cus (S \<inter> {j. 0 < a j}) a ?c" using
      KL_cus_pos_gen[
      OF finite_Int[OF disjI1, of S, of "{j. 0 < a j}"], of a, of ?c
      ] 1 2 3
        by (metis fin)
      have fstdb: "0 < setsum d (S \<inter> {i. 0 < a i})" using non_null(2) False
        by (metis Int_Collect fin finite_Int setsum_pos)
      have "(\<And>i. i \<in> S \<inter> {i. 0 < a i} \<Longrightarrow> 0 < a i) \<Longrightarrow>
    (\<And>i. i \<in> S \<inter> {i. 0 < a i} \<Longrightarrow> 0 < d i / setsum d (S \<inter> {i. 0 < a i})) \<Longrightarrow>
      setsum a (S \<inter> {i. 0 < a i}) = 1 \<Longrightarrow>
    (\<Sum>i\<in>S \<inter> {i. 0 < a i}. d i / setsum d (S \<inter> {i. 0 < a i})) = 1 \<Longrightarrow>
      0 \<le> KL_cus (S \<inter> {i. 0 < a i}) a (\<lambda>i. d i / setsum d (S \<inter> {i. 0 < a i}))"
        using KL_cus_pos_gen[
      OF finite_Int[OF disjI1, OF fin], of "{i. 0 < a i}", of "a", of "?c"
      ] by simp
      hence 6: "
      0 \<le> KL_cus (S \<inter> {i. 0 < a i}) a (\<lambda>i. d i / setsum d (S \<inter> {i. 0 < a i}))"
        using 2 3 5
        by simp
      have
      "(\<And>i. i \<in> S \<inter> {j. 0 < a j} \<Longrightarrow> 0 < d i) \<Longrightarrow>
      0 < setsum d (S \<inter> {i. 0 < a i}) \<Longrightarrow>
      setsum d (S \<inter> {i. 0 < a i}) \<le> 1 \<Longrightarrow>
    (\<And>i. i \<in> S \<inter> {j. 0 < a j} \<Longrightarrow> 0 \<le> a i) \<Longrightarrow>
      KL_cus (S \<inter> {j. 0 < a j}) a
    (\<lambda>i. d i / setsum d (S \<inter> {i. 0 < a i}))
      \<le> KL_cus (S \<inter> {j. 0 < a j}) a d"
        using KL_cus_mul
        by fastforce
      hence "setsum d (S \<inter> {i. 0 < a i}) \<le> 1 \<Longrightarrow>
    (\<And>i. i \<in> S \<inter> {j. 0 < a j} \<Longrightarrow> 0 \<le> a i) \<Longrightarrow>
      KL_cus (S \<inter> {j. 0 < a j}) a
    (\<lambda>i. d i / setsum d (S \<inter> {i. 0 < a i}))
      \<le> KL_cus (S \<inter> {j. 0 < a j}) a d" using non_null(2) fstdb
        by simp
      hence
      "(\<And>i. i \<in> S \<inter> {j. 0 < a j} \<Longrightarrow> 0 \<le> a i) \<Longrightarrow> KL_cus (S \<inter> {j. 0 < a j}) a
    (\<lambda>i. d i / setsum d (S \<inter> {i. 0 < a i}))
      \<le> KL_cus (S \<inter> {j. 0 < a j}) a d" using setsum.inter_restrict[OF fin, of d, of "{i. 0 < a i}"]
      setsum_mono[of S, of "(\<lambda>x. if x \<in> {i. 0 < a i} then d x else 0)", of d] non_null(2) sum_c_one
        by force
      hence
      "KL_cus (S \<inter> {j. 0 < a j}) a (\<lambda>i. d i / setsum d (S \<inter> {i. 0 < a i})) \<le> KL_cus (S \<inter> {j. 0 < a j}) a d"
        using non_null by simp
      moreover have "0 \<le> KL_cus (S \<inter> {j. 0 < a j}) a (\<lambda>i. d i / setsum d (S \<inter> {i. 0 < a i}))"
        using KL_cus_pos_gen[ OF finite_Int[OF disjI1, OF fin]] using 2 3 5 by fastforce
      ultimately show "0 \<le> KL_cus (S \<inter> {j. 0 < a j}) a d" by simp
  qed
    ultimately show ?thesis by simp
qed

(* Used in many theorems... *)
lemma sum_div_1:
  fixes f::"'b \<Rightarrow> 'c::field"
  assumes "(\<Sum>i\<in>A. f i) \<noteq> 0"
  defines "S \<equiv> \<Sum>i\<in>A. f i"
shows "(\<Sum>i\<in>A. f i / S) = 1"
    by (metis (no_types) S_def assms right_inverse_eq setsum_divide_distrib)

(*
_Kraft inequality for real codes using the McMillan theorem
*)
theorem rate_lower_bound :
  defines "l \<equiv> (\<lambda>i. cw_len i)"
  defines "LL \<equiv> L - {i. fi i = 0}"
  defines "F \<equiv> (X ` space M)"
shows "H \<le> cr"
proof -
    let ?c = "kraft_sum"
    let ?r = "(\<lambda>i. 1 / ((b powr l i) * ?c))"
    {
    fix i
    assume "i \<in> L"
    hence "0 \<le> fi i" using simple_distributed_nonneg[OF distr_i] bounded_input by blast
    } hence pos_pi: "\<And>i. i \<in> L \<Longrightarrow> 0 \<le> fi i" by simp
    {
    fix i
    assume iL: "i \<in> L"
    hence
    "fi i * (log b (1 / (1 / b powr (l i))) + log b (fi i))
    = fi i * log b (fi i / (1 / b powr (l i)))"
      using log_mult_ext2[OF pos_pi] powr_gt_zero b_gt_1
      by (simp add:
    `\<And>y i. \<lbrakk>i \<in> L; 0 < y\<rbrakk> \<Longrightarrow> fi i * log b (fi i * y) = fi i * log b (fi i) + fi i * log b y`
    iL linordered_field_class.sign_simps(36))
    }
    hence eqpi:
    "\<And>i. i\<in> L \<Longrightarrow> fi i * (log b (1 / (1 / b powr (l i))) + log b (fi i))
    = fi i * log b (fi i / (1 / b powr (l i)))"
      by simp
    have sum_one: "(\<Sum> i \<in> F. fi i) = 1"
      using simple_distributed_setsum_space[OF distr_i] F_def by simp
    hence sum_one_L: "(\<Sum> i \<in> L. fi i) = 1" using bounded_input F_def by simp
    {
    fix i
    assume iL: "i \<in> L"
    have
    "fi i * log b (fi i * ?c / (1/b powr l i) * (inverse kraft_sum)) =
    fi i * log b (fi i * ?c / (1/b powr l i)) + fi i * log b (inverse kraft_sum)"
      using log_mult_ext_3[OF pos_pi[OF iL]
    positive_imp_inverse_positive[OF kraft_sum_nonnull],
    of "kraft_sum / (1 / b powr (l i))"] divide_pos_pos[OF kraft_sum_nonnull] powr_gt_zero[of b]
    Orderings.order_class.order.strict_implies_not_eq[
    OF Orderings.order_class.order.strict_trans[OF zero_less_one, OF b_gt_1]
    ]
      by (metis (no_types) divide_1 inverse_divide inverse_positive_iff_positive times_divide_eq_right)
    } hence big_eq:
    "\<And>i. i \<in> L \<Longrightarrow> fi i * log b (fi i * ?c / (1/b powr l i) * (1 / kraft_sum)) =
    fi i * log b (fi i * ?c / (1/b powr l i)) + fi i * log b (1 / kraft_sum)"
      by (simp add: inverse_eq_divide)
    have 1: "cr - H = (\<Sum>i \<in> L. fi i * l i) + (\<Sum>i \<in> L. fi i * log b (fi i))"
      using kraft_sum_def entropy_rewrite cr_rw bounded_input l_def by simp
    also have 2: "(\<Sum>i\<in>L. fi i * l i) = (\<Sum>i \<in> L. fi i * (-log b (1/(b powr (l i)))))"
      using b_gt_1 log_divide by simp
    also have "\<dots> = -1 * (\<Sum>i \<in> L. fi i * (log b (1/(b powr (l i)))))"
      using setsum_right_distrib[of "-1" "(\<lambda>i. fi i * (- 1 * log b (1 / b powr (l i))))" L]
      by simp
    finally have
    "cr - H = -(\<Sum>i \<in> L. fi i * log b (1/b powr l i)) + (\<Sum>i \<in> L. fi i * log b (fi i))"
      by simp
    have "cr - H = (\<Sum>i \<in> L. fi i * ((log b (1/ (1/(b powr (l i))))) +log b (fi i)))"
      using b_gt_1 1
      by (simp add: distrib_left setsum.distrib)
    also have "\<dots> = (\<Sum>i \<in> L. fi i *((log b (fi i / (1/(b powr (l i)))))))"
      using Cartesian_Euclidean_Space.setsum_cong_aux[OF eqpi] by simp
    also from big_eq have
    "\<dots> = (\<Sum>i\<in>L. fi i * (log b (fi i * ?c / (1 / b powr (l i))))) + (\<Sum>i \<in> L. fi i) * log b (1/ ?c)"
      using kraft_sum_nonnull
      by (simp add: setsum_left_distrib setsum.distrib)
    also have "\<dots> = (\<Sum>i\<in>L. fi i * (log b (fi i * ?c / (1 / b powr (l i))))) - log b (?c)"
      using kraft_sum_nonnull
      by (simp add: log_inverse_eq divide_inverse sum_one_L)
    also have "\<dots> = (\<Sum> i \<in> L. fi i * log b (fi i / ?r i)) - log b (?c)"
      by (metis (mono_tags, hide_lams) divide_divide_eq_left divide_divide_eq_right)
    also have "\<dots> = KL_cus L fi ?r + log b (inverse ?c)"
      using b_gt_1 kraft_sum_nonnull by (simp add: log_inverse KL_cus_def)
    finally have code_ent_kl_log: "cr - H = KL_cus L fi ?r + log b (inverse ?c)" by simp
    have "setsum ?r L = 1"
      using sum_div_1[of "\<lambda>i. 1 / (b powr (l i))"] kraft_sum_nonnull l_def kraft_sum_powr
      by simp
    moreover have "\<And>i. 0 < ?r i" using b_gt_1 kraft_sum_nonnull by simp
    moreover have "(\<Sum>i\<in>L. fi i) = 1" using sum_one_L by simp
    ultimately have "0 \<le> KL_cus L fi ?r"
      using KL_cus_pos2[OF fin_L fi_pos _ _ _] by simp
    hence "log b (inverse ?c) \<le> cr - H" using code_ent_kl_log by simp
    hence "log b (inverse (kraft_sum)) \<le> cr - H" by simp
    moreover from McMillan assms have "0 \<le> log b (inverse (kraft_sum))"
      using kraft_sum_nonnull unfolding kraft_inequality_def
      by (simp add: b_gt_1 log_inverse_eq)
    ultimately show ?thesis by simp
qed
end
end
