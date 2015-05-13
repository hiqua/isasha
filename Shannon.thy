theory Shannon
imports "~~/src/HOL/Probability/Information"
begin
(*
AIM: Formalize Shannon's theorems
*)

subsection{* Basic types and helpers *}

type_synonym bit = bool
type_synonym bword = "bit list"
type_synonym letter = nat
type_synonym word = "letter list"

type_synonym encoder = "word \<Rightarrow> bword"
type_synonym decoder = "bword \<Rightarrow> word option"
type_synonym code = "encoder * decoder"

subsection{* First locale, generic to both Shannon's theorems *}
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
TODO: explain a lil more
TODO: link between bword and the variable b
*)

type_synonym prob = "letter \<Rightarrow> real"

(* locale generic to both theorems *)
locale information_space_discrete = information_space +
(* channnel *)
fixes Input :: "nat \<Rightarrow> ('a \<Rightarrow> letter)"
fixes input_bound :: letter
fixes Output :: "nat \<Rightarrow> ('a \<Rightarrow> letter)"
fixes fi :: "prob"
fixes fo :: "prob"
(* fixes N :: "'a measure" --"we should take M? ----> yes!" *)
fixes N' :: "letter measure"
fixes letters :: "nat set"
assumes distr_i:
"simple_distributed M (Input i) fi"
assumes distr_o:
"simple_distributed M (Output i) fo"
assumes memoryless:
"(m \<noteq> n \<longrightarrow> (indep_var N' (Input m) N' (Output n)) \<and> indep_var N' (Output m) N' (Output n))"
assumes mutual_info:
"\<I>(Input n ; Output n) > 0"
(* According to RAHM, this should be a rat, I'll look into this later *)
fixes source_entropy::real

(*
The entropy depends on the value of b, which is the cardinal of the available
output symbols.
*)
assumes binary_space: "b = 2"
assumes entropy_defi: "source_entropy = \<H>(Input 0)"
assumes letters_def: "letters = {0..input_bound}"
(* assumes bounded_input: "fi input_bound \<noteq> 0 \<and> (input_bound < n \<longrightarrow> fi n = 0)" *)
assumes bounded_input: "\<And>i. (Input i) ` space M = letters"
assumes bounded_input_alt: "\<And>n. n \<notin> letters \<Longrightarrow> fi n = 0"
(* TODO: check if this assumption is not redundant, i.e. simple_distributed \<Longrightarrow>? positive function *)
assumes fi_pos: "\<And>i. 0 \<le> fi i"

(* What is countable exactly? *)
assumes countable: "count_space (space M) = M"

print_locale information_space_discrete

(*
TODO: Have some predicates to
allow reasonings about codes. Keep the input_block_size that limits the size of the input, and use it.
*)
(*
 We will generalize the type "code" to any input by splitting the input in piece of length below a constant
*)
subsection{* locale specific to the source coding theorem *}
locale information_space_discrete_source = information_space_discrete +
fixes input_block_size::nat
begin
abbreviation "L \<equiv> letters"

definition lossless_code :: "code \<Rightarrow> bool" where
"lossless_code c = (\<forall>x. snd c (fst c x) = Some x)"

definition non_singular_code :: "code \<Rightarrow> bool" where
"non_singular_code c = (\<forall>x. \<forall>y. length x \<le> input_block_size \<and> length y \<le> input_block_size \<longrightarrow> snd c (fst c x) = snd c (fst c y) \<longrightarrow> x =y)"

(*
The definition automatically provides us with the extension of the code, we make
sure this extension is sound.
*)
definition block_encoding_code :: "code \<Rightarrow> bool" where
"block_encoding_code c = (\<forall>x. length x = input_block_size \<longrightarrow> (\<forall>xs. (fst c) (x @ xs) = (fst
c) x @ (fst c) xs))"

(*
Concatenated code: code taken by encoding each letter and concatenate the result
*)
definition concat_code :: "code \<Rightarrow> bool" where
  "concat_code c = (\<forall>x. fst c x = (fst c) [(hd x)] @ (fst c) (tl x))"

(*
A code is uniquely decodable iff its concatenation is non-singular
*)
definition u_decodable :: "code \<Rightarrow> bool" where
"u_decodable c = (\<forall>x. \<forall>y. snd c (fst c x) = snd c (fst c y) \<longrightarrow> x = y)"

abbreviation real_word :: "word \<Rightarrow> bool" where
"real_word w \<equiv> (set w \<subseteq> letters)"


abbreviation k_words :: "nat \<Rightarrow> word set" where
"k_words k \<equiv> {w. length w = k \<and> real_word w}"

lemma rw_tail: "real_word w \<Longrightarrow> w = [] \<or> real_word (tl w)"
by (metis dual_order.trans list.collapse set_subset_Cons)

(*
Is the code a real source encoding code?
_lossless
_uniquely decodable
*)
definition real_code ::"code \<Rightarrow> bool" where
"real_code c = ((lossless_code c) \<and> (\<forall>w. (fst c) w = [] \<longleftrightarrow> w = []) \<and> concat_code c)"

(*
length of the codeword associated with the letter
*)
definition cw_len :: "code \<Rightarrow> letter \<Rightarrow> nat" where
"cw_len c l = length ((fst c) [l])"

(*
The code rate is the expectation of the length of the code taken on all inputs (which is a finite set, the set of letters).
*)
  definition code_rate :: "code \<Rightarrow> real" where
"code_rate c = expectation (\<lambda>a. (cw_len c ((Input 0) a)))"


(*
Proof by Johannes Hölzl
*)
lemma (in prob_space) simp_exp:
  assumes X: "simple_distributed M X Px"
  shows "expectation X = (\<Sum>x \<in> X`space M. x * Px x)"
  using simple_distributed_finite[OF X]
using distributed_integral[OF simple_distributed[OF X], of "\<lambda>x. x"]
  by (simp add: lebesgue_integral_count_space_finite ac_simps)

lemma (in prob_space) simp_exp_composed:
  assumes X: "simple_distributed M X Px"
  shows "expectation (\<lambda>a. f (X a)) = (\<Sum>x \<in> X`space M. f x * Px x)"
using distributed_integral[OF simple_distributed[OF X], of f]
  by (simp add: lebesgue_integral_count_space_finite[OF simple_distributed_finite[OF X]] ac_simps)

(* lebesgue_integral_count_space_finite *)
(* nn_integral_count_space *)
  (* shows "(\<integral>x. f x \<partial>count_space A) = (\<Sum>a | a \<in> A \<and> f a \<noteq> 0. f a)" *)
lemma code_rate_rw:
"code_rate c = (\<Sum>i \<in> Input 0 ` space M. fi i * cw_len c i)" unfolding code_rate_def
using simp_exp_composed[where X="Input 0" and f = "cw_len c"]
by (metis (erased, lifting) distr_i mult.commute setsum.cong)



abbreviation cw_len_concat :: "code \<Rightarrow> word \<Rightarrow> nat" where
"cw_len_concat c w \<equiv> foldr (\<lambda>x s. (cw_len c x) + s) w 0"

lemma maj_fold:
fixes f::"letter \<Rightarrow> nat"
assumes "\<And>l. l\<in>letters \<Longrightarrow> f l \<le> bound"
shows "real_word w \<Longrightarrow> foldr (\<lambda>x s. f x + s) w 0 \<le> length w * bound"
proof (induction w)
case Nil
thus ?case by simp
next
case (Cons x xs)
assume "real_word (x#xs)"
moreover hence "real_word xs" by simp
moreover have "foldr (\<lambda>x s. f x + s) (x#xs) 0 = foldr (\<lambda>x s. f x + s) (xs) 0 +
f x" by simp
ultimately show ?case using assms Cons.IH by fastforce
qed

definition max_len :: "code \<Rightarrow> nat" where
"max_len c = Max ((\<lambda>x. cw_len c x) ` {n. n \<le> input_bound})"

lemma max_cw:
"\<And>l. l \<in> letters \<Longrightarrow> cw_len c l \<le> max_len c"
apply (simp add: letters_def max_len_def)
done


definition kraft_sum :: "code \<Rightarrow> real" where
"kraft_sum c = (\<Sum>i\<in>letters. 1 / b^(cw_len c i))"

lemma fin_letters: "finite letters" by (simp add:letters_def)
lemma emp_letters: "letters \<noteq> {}" by (simp add: letters_def)
lemma pos_cw_len: "\<And>i. 0 < 1 / b ^ cw_len c i" using binary_space by simp

lemma kraft_sum_nonnull: "\<And>c. 0 < kraft_sum c" using kraft_sum_def letters_def binary_space
Groups_Big.ordered_comm_monoid_add_class.setsum_pos[OF fin_letters emp_letters pos_cw_len] by simp

definition kraft_inequality :: "code \<Rightarrow> bool" where
"kraft_inequality c = (kraft_sum c \<le> 1)"


lemma k_words_rel:
  "\<And>k. k_words (Suc k) = {w. (hd w \<in> letters \<and> tl w \<in> k_words k \<and> w \<noteq> [])}"
proof
fix k
show "k_words (Suc k) \<subseteq> {w. (hd w \<in> letters \<and> tl w \<in> k_words k \<and> w \<noteq> [] )}" (is "?l \<subseteq> ?r")
proof
  fix w
  assume "w \<in> k_words (Suc k)"
  note asm = this
  hence "real_word w" by simp
  hence "hd w \<in> letters" using letters_def
  by (metis (mono_tags) asm hd_in_set list.size(3) mem_Collect_eq nat.distinct(1) subset_code(1))
  moreover have len: "length w = Suc k" using asm by simp
  moreover hence "w \<noteq> []" by auto
  moreover have "length (tl w) = k" using len by simp
  moreover have "real_word (tl w)" using asm
  by (metis `real_word w` calculation(2) list.size(3) nat.distinct(1) rw_tail)
  ultimately show "w \<in> ?r" using asm by simp
qed
next
fix k
show "k_words (Suc k) \<supseteq> {w. (hd w \<in> letters \<and> tl w \<in> k_words k \<and> w \<noteq> [])}"
proof
  fix w
  assume "w \<in> {w. hd w \<in> letters \<and> tl w \<in> {w. length w = k \<and> real_word w} \<and> w \<noteq>
  []}"
  note asm = this
  hence " hd w \<in> letters \<and> length (tl w) = k \<and> real_word (tl w)" by simp
  hence "real_word w"
  by (metis empty_iff insert_subset list.collapse list.set(1) set_simps(2) subsetI)
  moreover hence "length w = Suc k" using asm by auto
  ultimately show "w \<in> k_words (Suc k)" by simp
qed
qed

(* TODO: remove this version and prefer the alt one *)
lemma bij_k_words:
  shows "\<forall>k. bij_betw (\<lambda>wi. Cons (fst wi) (snd wi)) (letters \<times> (k_words k))  (k_words (Suc
  k))" unfolding bij_betw_def
proof
fix k
let ?f = "(\<lambda>wi. Cons (fst wi) (snd wi))"
let ?S = "letters \<times> (k_words k)"
let ?T = "k_words (Suc k)"
have inj: "inj_on ?f ?S" unfolding inj_on_def by simp
moreover have surj: "?f`?S = ?T"
proof (rule ccontr)
assume "?f ` ?S \<noteq> ?T"
  hence "\<exists>w. w\<in> ?T \<and> w \<notin> ?f`?S" by auto
  then obtain w where "w\<in> ?T \<and> w \<notin> ?f`?S" by blast
  note asm = this
  hence "w = ?f ((hd w),(tl w))" using k_words_rel by simp
  moreover have "((hd w),(tl w)) \<in> ?S" using k_words_rel asm by simp
  ultimately have "w \<in> ?f`?S" by blast
  thus "False" using asm by simp
qed
ultimately show "inj_on (\<lambda>wi. fst wi # snd wi) (letters \<times> {w. length w = k \<and> real_word w}) \<and>
    (\<lambda>wi. fst wi # snd wi) ` (letters \<times> {w. length w = k \<and> real_word w}) =
    {w. length w = Suc k \<and> real_word w}" using inj surj by simp
qed

lemma bij_k_words_alt:
  shows "\<And>k. bij_betw (\<lambda>wi. Cons (fst wi) (snd wi)) (letters \<times> (k_words k))  (k_words (Suc
  k))" using bij_k_words
by auto

lemma finite_k_words: "finite (k_words k)"
proof (induct k)
case 0
show ?case by simp
case (Suc n)
thus ?case using bij_k_words_alt bij_betw_finite letters_def by blast
qed

lemma cartesian_product:
  fixes f::"('c \<Rightarrow> real)"
  fixes g::"('b \<Rightarrow> real)"
  shows "finite A \<Longrightarrow> finite B \<Longrightarrow>
(\<Sum>b\<in>B. g b)* (\<Sum>a\<in>A. f a) = (\<Sum>ab\<in>A\<times>B. f (fst ab) * g (snd ab))"
using bilinear_times bilinear_setsum[where h="(\<lambda>x y. x * y)" and f="f"
  and g="g"]
by (metis (erased, lifting) setsum.cong split_beta' Groups.ab_semigroup_mult_class.mult.commute)

lemma kraft_sum_power :
shows "kraft_sum c^k = (\<Sum>w \<in> (k_words k). 1 / b^(cw_len_concat c w))"
proof (induct k)
case 0
have "k_words 0 = {[]}" by auto
thus ?case by simp
next
case (Suc n)
have "kraft_sum c^Suc n = kraft_sum c^n * kraft_sum c" by simp
also have "\<dots> =
(\<Sum>w \<in> k_words n. 1 / b^cw_len_concat c w) * (\<Sum>i\<in>letters. 1 / b^cw_len c i)"
by (metis Suc kraft_sum_def)
also have
"\<dots> =
(\<Sum>wi \<in> letters \<times> k_words n. 1/b^cw_len c (fst wi) * (1 / b^cw_len_concat c (snd wi)))"
using letters_def finite_k_words[where k="n"] cartesian_product[where A="letters"]
by fastforce
also have "\<dots> =
(\<Sum>wi \<in> letters \<times> k_words n. 1 / b^(cw_len_concat c (snd wi) + cw_len c (fst wi)))"
using letters_def binary_space power_add
by (metis (no_types, lifting) add.commute power_one_over)
also have "\<dots> =
(\<Sum>wi \<in> letters \<times> k_words n. 1 / b^cw_len_concat c (fst wi # snd wi))"
by (metis (erased, lifting) add.commute comp_apply foldr.simps(2))
also have "\<dots> = (\<Sum>w \<in> (k_words (Suc n)). 1 / b^(cw_len_concat c w))"
using bij_k_words_alt setsum.reindex_bij_betw by fastforce
finally show ?case by simp
qed



lemma bound_len_concat:
 shows "\<And>w. w \<in> k_words k \<Longrightarrow> cw_len_concat c w \<le> k * max_len c"
using max_cw maj_fold by blast


subsection{* Inequality of the kraft sum (source coding theorem, direct) *}


lemma sum_vimage_proof:
fixes g::"nat \<Rightarrow> real"
assumes bounded: "\<And>w. f w < bd"
shows "finite H \<Longrightarrow> (\<Sum>w\<in>H. g (f w)) = (\<Sum> m=0..<bd. (card ((f-`{m}) \<inter> H) )* g
m)" (is "?fin \<Longrightarrow> ?s1 = (\<Sum> m=0..<bd. ?ff m H)")
proof (induct H rule: finite_induct)
case empty
show ?case by simp
next
case (insert x F)
let ?rr = "(\<Sum>m = 0..<bd. ?ff m (insert x F))"
(* focusing of the right hand term *)
have "(f x) \<in> {0..<bd}" using assms by simp
hence sum_reord: "\<And> h::(nat \<Rightarrow> real). (\<Sum>m=0..<bd. h m) =
(setsum h ({0..<bd} - {f x}) + h (f x))"
by (metis diff_add_cancel finite_atLeastLessThan setsum_diff1_ring)
moreover have "\<And>n r. real ((n::nat) + 1) * r = (n* r + r)"
by (metis Suc_eq_plus1 distrib_left mult.commute mult.right_neutral real_of_nat_Suc)
ultimately have
"(\<Sum>m = 0..<bd. ?ff m (insert x F))
= (\<Sum>m\<in>{0..<bd} - {f x}. ?ff m (insert x F)) +
card (f -` {f x} \<inter> F) * g (f x) + g (f x)"
using insert by fastforce
hence "(\<Sum>m = 0..<bd. ?ff m (insert x F)) = (\<Sum>m\<in>{0..<bd}. ?ff m F) + g (f x)"
using assms sum_reord by fastforce
thus ?case using insert.hyps by simp
qed


lemma sum_vimage:
fixes g::"nat \<Rightarrow> real"
assumes bounded: "\<And>w. w \<in> H \<Longrightarrow> f w < bd" and "0 < bd"
shows "finite H \<Longrightarrow> (\<Sum>w\<in>H. g (f w)) = (\<Sum> m=0..<bd. (card ((f-`{m}) \<inter> H) ) * g m)"
(is "?fin \<Longrightarrow> ?s1 = ?s2")
proof -
let ?ff = "(\<lambda>x. if x\<in>H then f x else 0)"
let ?ss1 = "(\<Sum>w\<in>H. g (?ff w))"
have eq1: "?s1 =?ss1" by simp
let ?ss2 = "(\<Sum> m=0..<bd. (card ((?ff-`{m}) \<inter> H) ) * g m)"
have"\<And>m. ?ff -`{m} \<inter> H = f-`{m} \<inter> H" by auto
hence eq2: "?s2 = ?ss2" by simp
have boundedff: "\<And>w . ?ff w < bd" using assms by simp
hence "?fin \<Longrightarrow> ?ss1 = ?ss2"
using boundedff local.sum_vimage_proof[where f="?ff" and bd="bd"] assms
by blast
thus "?fin \<Longrightarrow> ?s1 = ?s2" using eq1 eq2 assms boundedff
by metis
qed



(*
5.54
*)
lemma kraft_sum_rewrite :
 "(\<Sum>w \<in> (k_words k). 1 / b^(cw_len_concat c w)) =
(\<Sum>m=0..<Suc (k*max_len c). card (k_words k \<inter> ((cw_len_concat c) -` {m})) * (1 /
b^m))" (is "?L = ?R")
proof -
have "\<And>w. w \<in> k_words k \<Longrightarrow> cw_len_concat c w < Suc ( k * max_len c)"
using bound_len_concat
by (metis le_antisym lessI less_imp_le_nat not_less_eq)
moreover have
"?R = (\<Sum>m = 0..<Suc (k * max_len c).
(card (cw_len_concat c -` {m} \<inter> k_words k)) * (1 / b ^ m))"
using Set.Int_commute
by metis
moreover have "0 < Suc (k*max_len c)" by simp
ultimately show ?thesis
using finite_k_words
sum_vimage[where f="cw_len_concat c" and g = "(\<lambda>i. 1/ (b^i))" and H ="k_words k"
and bd = "Suc (k*max_len c)"]
by simp
qed

definition set_of_k_words_length_m :: "code \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> word set" where
"set_of_k_words_length_m c k m = { xk. xk \<in> k_words k} \<inter> (cw_len_concat c)-`{m}"


(* REFACTOR BEGIN *)
lemma am_inj_code :
assumes lossless: "lossless_code c"
shows "inj_on (fst c) ((cw_len_concat c)-`{m})" (is "inj_on ?enc ?s")
proof -
fix x y
let ?dec = "snd c"
have "x \<in> ?s \<and> y \<in> ?s \<and> ?enc x = ?enc y \<longrightarrow> ?dec (?enc x) = ?dec (?enc y)"
using assms lossless_code_def by auto
thus ?thesis
using inj_on_def[where f="?enc" and A="?s"]
by (metis lossless lossless_code_def option.inject)
qed

lemma img_inc:
assumes "real_code c"
shows "(fst c)`(cw_len_concat c)-`{m}  \<subseteq> {b. length b = m}"
using assms
unfolding cw_len_def real_code_def concat_code_def
by (metis list.distinct(1) list.sel)

lemma bool_list_fin:
"\<And>m. finite  {bl::(bool list). length bl = m}"
proof -
fix m
have "{bl. set bl \<subseteq> {True, False} \<and> length bl = m} = {bl. length bl= m}"
by auto
moreover have "finite  {bl. set bl \<subseteq> {True, False} \<and> length bl = m}"
by (metis (full_types) finite_code finite_lists_length_eq)
ultimately show "finite {bl::(bool list). length bl = m}" by simp
qed

lemma bool_lists_card:
shows "\<And>m. card {bl::(bool list). length bl = m} = b^m"
proof -
fix m
have "card {b. set b \<subseteq> {True,False} \<and> length b = m} = card {True,False}^m"
using card_lists_length_eq[where A="{True,False}"] by simp
moreover have "card {True, False} = b" using binary_space by simp
moreover have "\<And>d. d \<in> {c::(bool list). True} \<longleftrightarrow> set d \<subseteq> {True, False}" by auto
ultimately show "card {b::(bool list). length b = m} = b^m"  by simp
qed

lemma img_card:
assumes "real_code c"
shows "card (fst c`cw_len_concat c-`{m})  \<le> b^m"
proof -
have "\<And>m. card ((fst c)` (cw_len_concat c)-`{m})  \<le> card {b::(bool list). length b = m}"
proof -
fix m
show "card ((fst c)` (cw_len_concat c)-`{m})  \<le> card {b::(bool list). length b = m}" using bool_list_fin img_inc assms
card_mono
 by (metis (mono_tags))
qed
thus ?thesis using assms bool_lists_card binary_space
by (metis real_of_nat_le_iff)
qed

lemma am_maj_aux2:
assumes real_code: "real_code c"
shows "finite ((cw_len_concat c)-`{m}) \<and> (card ((cw_len_concat c)-`{m})) \<le> b^m"
proof -
have "finite ((fst c)`cw_len_concat c-`{m}) \<and> card (fst c`cw_len_concat c-`{m}) \<le> b^m"
proof -
  have "finite (fst c ` (\<lambda>w. foldr (\<lambda>x. op + (cw_len c x)) w 0) -` {m})"
  using bool_list_fin
  by (metis assms infinite_super img_inc)
  thus ?thesis using img_card assms by simp
qed
moreover have "\<And>x\<^sub>1 x\<^sub>2. card (fst x\<^sub>1 ` (\<lambda>R. foldr (\<lambda>R. op + (cw_len x\<^sub>1 R)) R 0) -` {x\<^sub>2}) =
card ((\<lambda>R. foldr (\<lambda>R. op + (cw_len x\<^sub>1 R)) R 0) -` {x\<^sub>2}) \<or> \<not> lossless_code x\<^sub>1"
using am_inj_code  card_image by blast
ultimately show ?thesis using assms unfolding real_code_def
by (metis card_0_eq card_infinite finite_imageI image_is_empty )
qed

lemma am_maj:
assumes real_code: "real_code c"
shows "card (set_of_k_words_length_m c k m)\<le> b^m" (is "?c \<le> ?b")
proof -
have "set_of_k_words_length_m c k m \<subseteq> (cw_len_concat c)-`{m}" using
set_of_k_words_length_m_def by simp
hence "card (set_of_k_words_length_m c k m) \<le> card ((cw_len_concat c)-`{m})"
using assms am_maj_aux2 Finite_Set.card_mono by blast
thus ?thesis
using assms am_maj_aux2[where m="m"] by fastforce
qed

(* REFACTOR END )*)

lemma empty_set_k_words:
 assumes "0 < k" and "real_code c"
 shows "set_of_k_words_length_m c k 0 = {}"
proof (rule ccontr)
assume "\<not> set_of_k_words_length_m c k 0 = {}"
hence "\<exists>x. x \<in> set_of_k_words_length_m c k 0" by auto
then obtain x where "x \<in> set_of_k_words_length_m c k 0" by auto
note x_def = this
hence "x \<noteq> []" unfolding set_of_k_words_length_m_def using assms by auto
moreover have
"cw_len_concat c (hd x#tl x) =  cw_len_concat c (tl x) + cw_len c (hd x)"
by (metis add.commute comp_apply foldr.simps(2))
moreover have "(fst c) [(hd x)] \<noteq> []" using assms unfolding real_code_def by
simp
moreover hence "0 < cw_len c (hd x)" using cw_len_def by simp
ultimately have "x \<notin> set_of_k_words_length_m c k 0" unfolding set_of_k_words_length_m_def
by simp
thus "False" using x_def by simp
qed


lemma kraft_sum_rewrite2:
assumes "0 < k" and "real_code c"
assumes lossless: "lossless_code c"
shows "(\<Sum>m=0..<Suc (k*max_len c). (card (set_of_k_words_length_m c k m))/ b^m) \<le> (k * max_len c)"
proof -
have "(\<Sum>m=1..<Suc (k*max_len c). (card (set_of_k_words_length_m c k m) / b^m)) \<le> (\<Sum>m=1..<Suc(k * max_len c). b^m / b^m)"
using assms am_maj[where c="c" and k="k" and m="m"] binary_space
Groups_Big.setsum_mono[ where K="{1..<Suc(k*max_len c)}" and f="(\<lambda>m. (card
(set_of_k_words_length_m c k m))/b^m)" and g="\<lambda>m. b^m /b^m"]
by (metis am_maj divide_le_eq_1_pos divide_self_if linorder_not_le order_refl zero_less_numeral zero_less_power)
moreover have"(\<Sum>m=1..<Suc(k * max_len c). b^m / b^m) = (\<Sum>m=1..<Suc(k
*max_len c). 1)"
using binary_space by simp
moreover have "(\<Sum>m=1..<Suc(k*max_len c). 1) =(k * max_len c)"
using assms by simp
ultimately have "(\<Sum>m = 1..<Suc (k * max_len c). (card (set_of_k_words_length_m c k
 m)) / b ^ m) \<le>(k * max_len c)"
by (metis One_nat_def card_atLeastLessThan card_eq_setsum diff_Suc_Suc
real_of_card)
then show ?thesis using empty_set_k_words assms
by (metis One_nat_def card_empty divide_1 power_0 real_of_nat_zero setsum_shift_lb_Suc0_0_upt)
qed

lemma kraft_sum_power_bound :
assumes real_code: "real_code c" and "0 < k"
shows "(kraft_sum c)^k \<le> (k * max_len c)"
proof -
show ?thesis using assms kraft_sum_power kraft_sum_rewrite
kraft_sum_rewrite2 empty_set_k_words unfolding set_of_k_words_length_m_def
real_code_def by simp
qed

lemma kraft_sum_posi:
  "0 \<le> kraft_sum c" unfolding kraft_sum_def
by (metis (erased, lifting) b_gt_1 divide_less_0_1_iff less_le_not_le not_le
  order.trans setsum_nonneg zero_le_one zero_le_power)

theorem McMillan :
shows "real_code c \<Longrightarrow> kraft_inequality c"
proof -
  assume "real_code c"
  hence ineq: "\<And>k. 0 < k \<Longrightarrow> (kraft_sum c) \<le> root k k * root k (max_len c)"
  using kraft_sum_posi kraft_sum_power_bound
  by (metis real_of_nat_mult real_root_mult real_root_le_iff real_root_power_cancel)
  moreover hence
  "0 < max_len c \<Longrightarrow> (\<lambda>k. root k k * root k (max_len c)) ----> 1"
  using LIMSEQ_root LIMSEQ_root_const tendsto_mult
  by fastforce
  moreover have "\<forall>n\<ge>1. kraft_sum c \<le> root n n * root n (max_len c)"
  using ineq by simp
  moreover have "max_len c = 0 \<Longrightarrow> kraft_sum c \<le> 1" unfolding
  kraft_inequality_def using ineq by fastforce
  ultimately have "kraft_sum c \<le> 1"
  using LIMSEQ_le_const by blast
  thus "kraft_inequality c" unfolding kraft_inequality_def by simp
qed



lemma entropy_rewrite:
shows "source_entropy = -(\<Sum>i \<in> letters. fi i * log b (fi i))"
proof -
have sum_set: "(Input 0) ` space M = letters" using bounded_input by simp
have "source_entropy = \<H>(Input 0)" using entropy_defi by simp
also have "\<dots> = entropy b (count_space ((Input 0)`space M)) (Input 0)" by simp
finally have "\<dots> =  -(\<Sum>i \<in> letters. fi i * log b (fi i))"
using distr_i entropy_simple_distributed sum_set by blast
thus ?thesis by (metis entropy_defi)
qed


lemma entropy_rw:
shows "source_entropy = -(\<Sum>i \<in> (Input 0) ` space M. fi i * log b (fi i))"
proof -
have "source_entropy = \<H>(Input 0)" using entropy_defi by simp
also have "\<dots> = entropy b (count_space ((Input 0)`space M)) (Input 0)" by simp
finally have "\<dots> =  -(\<Sum>i \<in> (Input 0) ` space M. fi i * log b (fi i))"
using distr_i entropy_simple_distributed by blast
thus ?thesis
by (metis entropy_defi)
qed

lemma log_mult_ext: "\<And>x y z. 0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> 0 < z \<Longrightarrow> x * log b (x*z*y) = x * log b (x*z) + x * log b y"
proof -
  fix x :: real and y :: real and z :: real
  assume a1: "0 < y"
  assume a2: "0 \<le> x"
  assume a3: "0 < z"
  moreover
  { assume "x * z \<noteq> 0"
    hence "x * (log b y + log b (x * z)) = x * log b (x * (y * z))" using a1 a2 a3 by (metis binary_space eq_numeral_simps(2) less_eq_real_def less_numeral_simps(4) log_mult mult.left_commute mult_nonneg_nonneg num.distinct(2)) }
  ultimately show "x * log b (x * z * y) = x * log b (x * z) + x * log b y" by (metis (no_types) add.commute distrib_left mult.commute mult.left_commute mult_zero_right nonzero_mult_divide_cancel_right order_less_irrefl)
qed

lemma log_mult_ext2: "\<And>x y. 0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> x * log b (x*y) = x * log b (x) + x * log b y"
proof -
fix x y::real
assume "0 \<le> x" "0 < y"
thus  "x * log b (x*y) = x * log b (x) + x * log b y" using log_mult_ext[of x, of y, of 1] by simp
qed

(*
TODO (eventually):
I use a custom definition of the KL_divergence, as it is far simpler for me to use. It'd be better
if in the end I can use the real def definition KL_cus
*)
definition KL_cus ::"letter set \<Rightarrow> (letter \<Rightarrow> real) \<Rightarrow> (letter \<Rightarrow> real) \<Rightarrow> real" where
  "KL_cus S a c = (\<Sum> i \<in> S. a i * log b (a i / c i))"

lemma KL_cus_mul:
  assumes "0 < d"
  assumes "d \<le> 1"
  assumes pos: "\<And>i. i\<in>S \<Longrightarrow> 0 \<le> a i" "\<And>i. i\<in>S \<Longrightarrow> 0 < c i"
  shows "KL_cus S a c \<ge> KL_cus S a (\<lambda>i. c i / d)"
unfolding KL_cus_def
proof -
{fix i
assume "i\<in>S"
note asm = this
hence "(a i / ((c i) / d)) \<le> (a i / c i)" using pos[OF asm] assms
by (metis (no_types) divide_1 frac_le less_imp_triv not_less)
hence "log b (a i / (c i / d)) \<le> log b (a i / c i)" using log_less[OF b_gt_1] assms asm
by (metis (full_types) b_gt_1 divide_divide_eq_left inverse_divide le_less_linear log_le log_neg_const order_refl times_divide_eq_right zero_less_mult_iff)
}
hence "\<And>i. i\<in>S \<Longrightarrow> log b (a i / (c i / d)) \<le> log b (a i / c i)"
using assms(2) assms(3) log_less
by simp
thus "(\<Sum>i\<in>S. a i * log b (a i / (c i / d)))
    \<le> (\<Sum>i\<in>S. a i * log b (a i / c i))"
by (meson mult_left_mono pos(1) setsum_mono)
qed


(*
proof -
have "(\<And>i. i \<in> S \<Longrightarrow>
          a i * log b (a i / (c i / d)) \<le> a i * log b (a i / c i)) \<Longrightarrow>
    (\<Sum>i\<in>S. a i * log b (a i / (c i / d)))
    \<le> (\<Sum>i\<in>S. a i * log b (a i / c i))"
using b_gt_1  assms setsum_mono[where f="(\<lambda>i. a i * log b (a i / (c i / d)))"
and K="S" and g="(\<lambda>i. a i * log b (a i / c i))"] log_le_cancel_iff[OF b_gt_1]
by simp
moreover have
"(\<And>i. i \<in> S \<Longrightarrow> a i * log b (a i / (c i * d)) \<le> a i * log b (a i / c i))"
using log_le_cancel_iff[OF b_gt_1]
*)

lemma KL_cus_pos:
  fixes a c::"letter \<Rightarrow> real"
  assumes fin: "finite S"
  assumes nemp: "S \<noteq> {}"
  assumes non_null: "\<And>i. i\<in>S \<Longrightarrow> 0 < a i" "\<And>i. i\<in> S \<Longrightarrow> 0 < c i"
  assumes sum_a_one: "(\<Sum> i \<in> S. a i) = 1"
  assumes sum_c_one: "(\<Sum> i \<in> S. c i) = 1"
  shows "0 \<le> KL_cus S a c" unfolding KL_cus_def
proof -
(* TODO: what is the elegant way to do this already? (fix variables and obtains assumptions
automatically) *)(*
assume non_null: "\<And>i. i\<in>letters \<Longrightarrow> 0 < a i" "\<And>i. i\<in> letters \<Longrightarrow> 0 < c i"
assume sum_a_one: "(\<Sum> i \<in> letters. a i) = 1"
assume sum_c_one: "(\<Sum> i \<in> letters. c i) = 1"*)
let ?f = "\<lambda>i. c i / a i"
have f_pos: "\<And>i. i\<in>S \<Longrightarrow> 0 < ?f i" using non_null by simp
have a_pos: "\<And>i. i\<in> S \<Longrightarrow> 0 \<le> a i" using non_null by (simp add: order.strict_implies_order)
have "- log b (\<Sum>i\<in>S. a i * c i / a i) \<le> (\<Sum>i\<in>S. a i * - log b (c i / a i))"
using convex_on_setsum[
OF fin,OF nemp,OF minus_log_convex[OF b_gt_1],OF convex_real_interval(3)[of 0],
OF sum_a_one, OF a_pos, where y="?f"
]
f_pos
by simp
also have "- log b (\<Sum>i\<in>S. a i * c i / a i) = -log b (\<Sum>i\<in>S. c i)"
by (smt non_null(1) nonzero_mult_divide_cancel_left setsum.cong)
finally have "0 \<le> (\<Sum>i\<in>S. a i * - log b (c i / a i))"using sum_c_one by simp
thus "0 \<le> (\<Sum>i\<in>S. a i * log b (a i / c i))"
using binary_space log_divide non_null(1) non_null(2) by auto
qed

lemma KL_cus_pos_emp:
  "0 \<le> KL_cus {} a c" unfolding KL_cus_def by simp

lemma KL_cus_pos_gen:
  fixes a c::"letter \<Rightarrow> real"
  assumes fin: "finite S"
  assumes non_null: "\<And>i. i\<in>S \<Longrightarrow> 0 < a i" "\<And>i. i\<in> S \<Longrightarrow> 0 < c i"
  assumes sum_a_one: "(\<Sum> i \<in> S. a i) = 1"
  assumes sum_c_one: "(\<Sum> i \<in> S. c i) = 1"
  shows "0 \<le> KL_cus S a c"
using KL_cus_pos KL_cus_pos_emp assms by metis

lemma KL_cus_pos2:
  fixes a c::"letter \<Rightarrow> real"
  assumes fin: "finite S"
  assumes non_null: "\<And>i. i\<in>S \<Longrightarrow> 0 \<le> a i" "\<And>i. i\<in> S \<Longrightarrow> 0 < c i"
  assumes sum_a_one: "(\<Sum> i \<in> S. a i) = 1"
  assumes sum_c_one: "(\<Sum> i \<in> S. c i) = 1"
  shows "0 \<le> KL_cus S a c"
proof -
have "S = (S \<inter> {i. 0 < a i}) \<union> (S \<inter> {i. 0 = a i})" using non_null(1)
by fastforce
moreover have "(S \<inter> {i. 0 < a i}) \<inter> (S \<inter> {i. 0 = a i}) = {}" by auto
ultimately have eq: "KL_cus S a c = KL_cus (S \<inter> {i. 0 < a i}) a c + KL_cus (S \<inter> {i. 0 = a i}) a c"
unfolding KL_cus_def
by (metis (mono_tags, lifting) fin finite_Un setsum.union_disjoint)
have "KL_cus (S \<inter> {i. 0 = a i}) a c = 0" unfolding KL_cus_def by simp
hence "KL_cus S a c = KL_cus (S \<inter> {i. 0 < a i}) a c" using eq by simp
moreover have "0 \<le> KL_cus (S \<inter> {i. 0 < a i}) a c"
proof(cases "(S \<inter> {i. 0 < a i}) = {}")
  case True
  then show ?thesis unfolding KL_cus_def by simp
next
  case False
  note asm = this
  let ?c = "\<lambda>i. c i / (\<Sum>j \<in>(S \<inter> {i. 0 < a i}). c j)"
(* a pos *)
  have 1: "(\<And>i. i \<in> S \<inter> {i. 0 < a i} \<Longrightarrow> 0 < a i)" by simp
(* ?c pos *)
  have 2: "(\<And>i. i \<in> S \<inter> {i. 0 < a i} \<Longrightarrow> 0 < ?c i)" using non_null
  by (smt divide_pos_pos empty_iff fin finite_Int inf_le1 setsum_pos subsetCE)
(* sum a equals to 1 *)
  have 3: "setsum a (S \<inter> {i. 0 < a i}) = 1" using sum_a_one non_null
  by (smt fin mem_Collect_eq setsum.cong setsum.inter_restrict)
  have "(\<Sum>i\<in>S \<inter> {j. 0 < a j}. ?c i) = (\<Sum>i\<in>S \<inter> {j. 0 < a j}. c i) / (\<Sum>i\<in>S \<inter> {j. 0 < a j}. c i)"
  by (metis setsum_divide_distrib)
(* sum ?c equals to 1 *)
  hence 5: "(\<Sum>i\<in>S \<inter> {j. 0 < a j}. ?c i) = 1"
  using "2" asm by force
  hence "0 \<le> KL_cus (S \<inter> {j. 0 < a j}) a ?c" using
  KL_cus_pos_gen[
    OF finite_Int[OF disjI1, of S, of "{j. 0 < a j}"], of a, of ?c
] 1 2 3
  by (metis fin)
 have fstdb: "0 < setsum c (S \<inter> {i. 0 < a i})" using non_null(2) asm
by (metis Int_Collect fin finite_Int setsum_pos)
have "(\<And>i. i \<in> S \<inter> {i. 0 < a i} \<Longrightarrow> 0 < a i) \<Longrightarrow>
    (\<And>i. i \<in> S \<inter> {i. 0 < a i} \<Longrightarrow> 0 < c i / setsum c (S \<inter> {i. 0 < a i})) \<Longrightarrow>
    setsum a (S \<inter> {i. 0 < a i}) = 1 \<Longrightarrow> (\<Sum>i\<in>S \<inter> {i. 0 < a i}. c i / setsum c (S \<inter> {i. 0 < a i})) = 1 \<Longrightarrow> 0 \<le> KL_cus (S \<inter> {i. 0 < a i}) a (\<lambda>i. c i / setsum c (S \<inter> {i. 0 < a i}))"
  using KL_cus_pos_gen[
      OF finite_Int[OF disjI1, OF fin], where G1="{i. 0 < a i}" and a="a" and c="?c"
  ]  by simp
hence 6: "
     0 \<le> KL_cus (S \<inter> {i. 0 < a i}) a (\<lambda>i. c i / setsum c (S \<inter> {i. 0 < a i}))"
using 2 3 5
by simp
 have
"(\<And>i. i \<in> S \<inter> {j. 0 < a j} \<Longrightarrow> 0 < c i) \<Longrightarrow>
    0 < setsum c (S \<inter> {i. 0 < a i}) \<Longrightarrow>
    setsum c (S \<inter> {i. 0 < a i}) \<le> 1 \<Longrightarrow>
    (\<And>i. i \<in> S \<inter> {j. 0 < a j} \<Longrightarrow> 0 \<le> a i) \<Longrightarrow>
    KL_cus (S \<inter> {j. 0 < a j}) a
     (\<lambda>i. c i / setsum c (S \<inter> {i. 0 < a i}))
    \<le> KL_cus (S \<inter> {j. 0 < a j}) a c"
using KL_cus_mul[where d = "setsum c (S \<inter> {i. 0 < a i})" and S = "(S \<inter> {j. 0 < a j})" and c="c" and a="a"]
  by simp
hence "setsum c (S \<inter> {i. 0 < a i}) \<le> 1 \<Longrightarrow>
    (\<And>i. i \<in> S \<inter> {j. 0 < a j} \<Longrightarrow> 0 \<le> a i) \<Longrightarrow>
    KL_cus (S \<inter> {j. 0 < a j}) a
     (\<lambda>i. c i / setsum c (S \<inter> {i. 0 < a i}))
    \<le> KL_cus (S \<inter> {j. 0 < a j}) a c" using non_null(2) 5 fstdb
by simp
hence "(\<And>i. i \<in> S \<inter> {j. 0 < a j} \<Longrightarrow> 0 \<le> a i) \<Longrightarrow> KL_cus (S \<inter> {j. 0 < a j}) a
     (\<lambda>i. c i / setsum c (S \<inter> {i. 0 < a i}))
    \<le> KL_cus (S \<inter> {j. 0 < a j}) a c" using sum_c_one non_null
by (smt fin setsum.inter_restrict setsum_mono)
hence "KL_cus (S \<inter> {j. 0 < a j}) a
     (\<lambda>i. c i / setsum c (S \<inter> {i. 0 < a i}))
    \<le> KL_cus (S \<inter> {j. 0 < a j}) a c" using non_null by simp
moreover have "0 \<le> KL_cus (S \<inter> {j. 0 < a j}) a
     (\<lambda>i. c i / setsum c (S \<inter> {i. 0 < a i}))" using KL_cus_pos_gen[ OF finite_Int[OF disjI1, OF fin],
where G1="{i. 0 < a i}" and a="a" and c="?c"] using 1 2 3 5
by blast
 ultimately show "0 \<le> KL_cus (S \<inter> {j. 0 < a j}) a c" by simp
qed
ultimately show ?thesis by simp
qed

lemma simp_posi:
  assumes "simple_distributed M X Px"
  shows "\<And>x. x \<in> X ` space M \<Longrightarrow> 0 \<le> Px x"
using assms simple_distributed_measure[OF assms]
by (metis measure_nonneg)

(*
_Kraft inequality for uniquely decodable codes using the McMillan theorem
*)
(* TODO using bounded_input, is that ok? *)
theorem rate_lower_bound :
assumes "real_code c"
defines "l \<equiv> (\<lambda>i. cw_len c i)"
defines "p \<equiv> (\<lambda>i. fi i)"
defines "LL \<equiv> L - {i. p i = 0}"
defines "F \<equiv> (Input 0 ` space M)"
shows "source_entropy \<le> code_rate c"
proof -
let ?c = "kraft_sum c"
let ?r = "(\<lambda>i. 1 / ((b powr l i) * ?c))"
{
fix i
assume "i \<in> letters"
(* TODO using bounded_input *)
hence "0 \<le> p i" using simple_distributed_nonneg[OF distr_i] p_def bounded_input by fast
} hence pos_pi: "\<And>i. i \<in> letters \<Longrightarrow> 0 \<le> p i" by simp
{
fix i
assume "i \<in> letters"
hence "p i * (log b (1 / (1 / b powr real (l i))) + log b (p i)) = p i * log b (p i / (1 / b powr real (l i)))"
using log_mult_ext2[OF pos_pi] powr_gt_zero
proof -
  have "1 < b"
    using b_gt_1 by blast
  thus ?thesis
    by (simp add: `\<And>y i. \<lbrakk>i \<in> L; 0 < y\<rbrakk> \<Longrightarrow> p i * log b (p i * y) = p i * log b (p i) + p i * log b y` `i \<in> L` linordered_field_class.sign_simps(36))
qed
}
hence eqpi: "\<And>i. i\<in> letters \<Longrightarrow> p i * (log b (1 / (1 / b powr real (l i))) + log b (p i)) = p i * log b (p i / (1 / b powr real (l i)))"
by simp
have sum_one: "(\<Sum> i \<in> F. p i) = 1"
using simple_distributed_setsum_space[OF distr_i[of 0]] p_def F_def by simp
(* TODO using bounded_input *)
hence sum_one_L: "(\<Sum> i \<in> L. p i) = 1" using bounded_input F_def by simp
{
fix i
assume "i \<in> letters"
note asm = this
have "p i * log b (p i * ?c / (1/b powr l i) * (1 / kraft_sum c)) =
p i * log b (p i * ?c / (1/b powr l i)) + p i * log b (1 / kraft_sum c)"
using log_mult_ext[OF pos_pi[OF asm], OF Fields.linordered_field_class.positive_imp_inverse_positive[OF kraft_sum_nonnull[of c]],
of "kraft_sum c / (1 / b powr real (l i))"]
  binary_space powr_gt_zero[of b, of "l i"]
using divide_pos_pos inverse_eq_divide kraft_sum_nonnull times_divide_eq_right
proof -
  have "\<not> 0 < kraft_sum c / inverse (b powr real (l i)) \<or> p i * log b (p i * (kraft_sum c / inverse (b powr real (l i)))) + p i * log b (inverse (kraft_sum c)) = p i * log b (p i * (kraft_sum c / inverse (b powr real (l i))) * inverse (kraft_sum c))"
    by (metis `0 < kraft_sum c / (1 / b powr real (l i)) \<Longrightarrow> p i * log b (p i * (kraft_sum c / (1 / b powr real (l i))) * inverse (kraft_sum c)) = p i * log b (p i * (kraft_sum c / (1 / b powr real (l i)))) + p i * log b (inverse (kraft_sum c))` inverse_eq_divide)
  hence "p i * log b (p i * kraft_sum c / b powr - real (l i)) + p i * log b (inverse (kraft_sum c)) = p i * log b (p i * kraft_sum c / b powr - real (l i) * inverse (kraft_sum c))"
    using binary_space kraft_sum_nonnull powr_minus by auto
  thus ?thesis
    by (simp add: inverse_eq_divide powr_minus)
qed
} then have big_eq: "\<And>i. i \<in> letters \<Longrightarrow> p i * log b (p i * ?c / (1/b powr l i) * (1 / kraft_sum c)) =
p i * log b (p i * ?c / (1/b powr l i)) + p i * log b (1 / kraft_sum c)" by simp
have 1: "code_rate c - source_entropy = (\<Sum>i \<in> L. p i * l i) + (\<Sum>i \<in> L. p i * log b (p i))"
unfolding code_rate_def entropy_def
using kraft_sum_def[where c="c"] entropy_rewrite bounded_input simp_exp_composed distr_i
using code_rate_def code_rate_rw bounded_input l_def p_def by auto
also have 2: "(\<Sum>i\<in>L. p i * l i) = (\<Sum>i \<in> L. p i * (-log b (1/(b powr (l i)))))"
 using binary_space
using log_divide by auto
also have "\<dots> =  (\<Sum>i \<in> L. p i * (-1 * log b (1/(b powr (l i)))))" by simp
also have "\<dots> = -1 * (\<Sum>i \<in> L. p i * (log b (1/(b powr (l i)))))"
using setsum_right_distrib[where r="-1" and A="L" and f="(\<lambda>i.  p i * (- 1 * log b (1 / b powr real (l i))))"]
by simp
finally have "code_rate c - source_entropy = -(\<Sum>i \<in> L. p i * log b (1/b powr l i)) + (\<Sum>i \<in> L. p i * log b (p i))" by simp
from 1 2 have "code_rate c - source_entropy = (\<Sum>i \<in> L. p i * (-log b (1/(b powr (l i))))) +  (\<Sum>i \<in> L. p i * log b (p i))" by simp
also have "\<dots> = (\<Sum>i \<in> L. p i * (log b (1/ (1/(b powr (l i)))))) +  (\<Sum>i \<in> L. p i * log b (p i))"
using log_inverse binary_space
using log_powr powr_minus_divide
by (metis (lifting) log_powr_cancel num.distinct(2) numeral_eq_one_iff zero_less_numeral)
also have "\<dots> = (\<Sum>i \<in> L. p i * (log b (1/ (1/(b powr (l i))))) + p i * log b (p i))"
by (simp add: setsum.distrib)
also have "\<dots> = (\<Sum>i \<in> L. p i * ((log b (1/ (1/(b powr (l i))))) +log b (p i)))"
by (metis (no_types, hide_lams) distrib_left)
also have "\<dots> = (\<Sum>i \<in> L. p i *((log b (p i / (1/(b powr (l i)))))))"
using Cartesian_Euclidean_Space.setsum_cong_aux[OF eqpi] by simp
also have "\<dots> = (\<Sum>i \<in> L. p i *((log b (p i * (?c * 1 / ?c) / (1/(b powr (l i)))))))"
using kraft_sum_nonnull[of c] by simp
also have "\<dots> = (\<Sum>i \<in> L. p i *((log b (p i * ?c / (1/b powr l i) * 1/?c))))" by simp
also from big_eq have "\<dots> = (\<Sum>i \<in> L. p i *((log b (p i * ?c  / (1/b powr l i)))) + (p i * log b (1/?c)))"
using add.commute distrib_left divide_divide_eq_right times_divide_eq_right by simp
also have "\<dots> = (\<Sum>i\<in>L. p i * (log b (p i * ?c / (1 / b powr real (l i))))) + (\<Sum>i \<in> L. p i * log b (1/ ?c))"
using Groups_Big.comm_monoid_add_class.setsum.distrib by simp
also have "\<dots> = (\<Sum>i\<in>L. p i * (log b (p i * ?c / (1 / b powr real (l i))))) + (\<Sum>i \<in> L. p i) * log b (1/ ?c)"
using setsum_left_distrib by (metis (no_types))
also have "\<dots> = (\<Sum>i\<in>L. p i * (log b (p i * ?c / (1 / b powr real (l i))))) + log b (1/?c)"
using sum_one_L by simp
also have "\<dots> = (\<Sum>i\<in>L. p i * (log b (p i * ?c / (1 / b powr real (l i))))) - log b (?c)"
using log_inverse_eq kraft_sum_nonnull
by (metis (no_types, lifting) add_uminus_conv_diff divide_inverse monoid_mult_class.mult.left_neutral)
also have "\<dots> = (\<Sum> i \<in> L. p i * log b (p i / ?r i)) - log b (?c)"
by (metis (mono_tags, hide_lams) divide_divide_eq_left divide_divide_eq_right)
also have "\<dots> = KL_cus L p ?r - log b ( ?c)" unfolding KL_cus_def using sum_one by simp
also have "\<dots> = KL_cus L p ?r + log b (inverse ?c)"
using log_inverse binary_space kraft_sum_nonnull by simp
finally have code_ent_kl_log: "code_rate c - source_entropy = KL_cus L p ?r + log b (inverse ?c)" by simp
{
} hence sum_r_one: "setsum ?r L = 1" sorry
have r_non_null: "\<And>i. 0 < ?r i" using b_gt_1
using kraft_sum_nonnull by auto
have sum_fi_one: "(\<Sum>i\<in>L. fi  i) = 1" using bounded_input sum_one_L unfolding p_def by simp
  have "0 \<le> KL_cus L p ?r"
using KL_cus_pos2[OF fin_letters, where a =fi and c="?r",OF fi_pos,OF r_non_null,OF sum_fi_one,OF sum_r_one]
unfolding F_def p_def by simp
hence "log b (inverse ?c) \<le> code_rate c -source_entropy" using code_ent_kl_log by simp


hence "log b (inverse (kraft_sum c)) \<le> code_rate c - source_entropy"
unfolding kraft_inequality_def p_def by simp

moreover from McMillan assms have "0 \<le> log b (inverse (kraft_sum c))"
using kraft_sum_nonnull unfolding kraft_inequality_def
by (metis b_gt_1 log_inverse_eq log_le_zero_cancel_iff neg_0_le_iff_le)
ultimately have "0 \<le> code_rate c - source_entropy" using McMillan assms by simp
thus ?thesis by simp
qed

end
end
