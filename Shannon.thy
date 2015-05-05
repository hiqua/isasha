theory Shannon
imports "~~/src/HOL/Probability/Information" "~~/src/HOL/Library/NthRoot_Limits"
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
assumes bounded_input: "(Input i) ` space M \<subseteq> letters"
assumes bounded_input_alt: "\<And>n. n \<notin> letters \<Longrightarrow> fi n = 0"


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
by (metis  list.sel_set(2) subset_code(1) subset_eq)

(*
Is the code a real source encoding code?
_lossless
_uniquely decodable
*)
definition real_code ::"code \<Rightarrow> bool" where
"real_code c = ((lossless_code c) \<and> (\<forall>w. (fst c) w = [] \<longleftrightarrow> w = []) \<and> concat_code c)"

(*
The code rate is the expectation of the length of the code taken on all inputs.
*)
definition code_rate :: "code \<Rightarrow> real" where
"code_rate code = lebesgue_integral M (\<lambda>a. (fi ((Input 0) a)) * (length ((fst
code) [(Input 0) a])))"

(*
length of the codeword associated with the letter
*)
definition cw_len :: "code \<Rightarrow> letter \<Rightarrow> nat" where
"cw_len c l = length ((fst c) [l])"


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
by (metis Suc_eq_plus1 add.commute
comm_semiring_1_class.normalizing_semiring_rules(3) real_of_nat_Suc)
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

(*
_Kraft inequality for uniquely decodable codes using the McMillan theorem
*)
theorem rate_lower_bound :
shows "real_code c \<Longrightarrow> source_entropy \<le> code_rate c"
proof sorry

(*
theorem kraft_theorem :
assumes "(\<Sum> k\<in>{0..< input_bound}. (1 / b^(lengthk k))) \<le> 1"
shows "\<exists>c. real_code c \<and> (k\<in>{0..<input_bound} \<longrightarrow> (cw_len c k) = lengthk k)"
proof sorry

theorem rate_upper_bound : "0 < \<epsilon> \<Longrightarrow> (\<exists>n. \<exists>c. n \<le> input_block_size \<Longrightarrow> (real_code c
\<and> code_rate c \<le> source_entropy + \<epsilon>))"
sorry
*)
end
end
