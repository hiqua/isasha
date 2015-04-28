theory Shannon
imports Information "~~/src/HOL/Library/NthRoot_Limits"
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
fixes N :: "'a measure" --"we should take M?"
fixes N' :: "letter measure"
fixes letters :: "nat set"
assumes distr_i:
"simple_distributed N (Input i) fi"
assumes distr_o:
"simple_distributed N (Output i) fo"
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
assumes letters_def: "letters = {0..<input_bound}"
assumes bounded_input: "fi input_bound \<noteq> 0 \<and> (input_bound < n \<longrightarrow> fi n = 0)"

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
"real_code c = ((lossless_code c) \<and> (\<forall>w. (fst c) w = [] \<longleftrightarrow> w = []))"

(*
The code rate is the expectation of the length of the code taken on all inputs.
*)
definition code_rate :: "code \<Rightarrow> real" where
"code_rate code = lebesgue_integral N (\<lambda>a. (fi ((Input 0) a)) * (length ((fst
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

(* should be easy by induction on k *)
lemma kraft_sum_power :
assumes "real_code c"
shows "(kraft_sum c) ^k = (\<Sum>w \<in> (k_words k). 1 / b^(cw_len_concat c w))"
proof sorry

lemma bound_len_concat:
 shows "\<And>w. w \<in> k_words k \<Longrightarrow> cw_len_concat c w \<le> k * max_len c"
using max_cw maj_fold by blast


subsection{* Inequality of the kraft sum (source coding theorem, direct) *}

(* TODO: insert this lemma in the following proof *)
lemma sum_vimage_proof_aux2:
"real ((n::nat) + 1) * r = (n* r + r)"
by (metis Suc_eq_plus1 add.commute comm_semiring_1_class.normalizing_semiring_rules(3) real_of_nat_Suc)

lemma sum_vimage_proof:
fixes g::"nat \<Rightarrow> real"
assumes bounded: "\<And>w. f w < bound"
shows "finite H \<Longrightarrow> (\<Sum>w\<in>H. g (f w)) = (\<Sum> m=0..<bound. (card ((f-`{m}) \<inter> H) )* g
m)" (is "?fin \<Longrightarrow> ?s1 = (\<Sum> m=0..<bound. ?ff m H)")
proof (induct H rule: finite_induct)
case empty
show ?case by simp
next
case (insert x F)
let ?rr = "(\<Sum>m = 0..<bound. ?ff m (insert x F))"
have lefthandterm: "(\<Sum>w\<in>insert x F. g (f w)) = (\<Sum>w\<in>F. g (f w)) + g (f x)"
using insert.hyps by simp
(* now focusing of the right hand term *)
have "finite F \<Longrightarrow> card (f -` {m} \<inter> insert x F) = (if f x = m then 1 + card (f -` {m} \<inter> F) else card (f -` {m} \<inter>F))"
using insert.hyps by simp
have "(f x) \<in> {0..<bound}" using assms by simp
hence "\<forall>h::(nat \<Rightarrow> real). (\<Sum>m=0..<bound. h m)- h (f x) = (\<Sum> m \<in> ({0..<bound} - {f x}). h m)"
by (metis finite_atLeastLessThan setsum_diff1_ring)
hence sum_reord: "\<And> h::(nat \<Rightarrow> real). (\<Sum>m=0..<bound. h m) = (setsum h ({0..<bound} - {f x}) + h (f x))"
by (metis diff_add_cancel)
have "?rr = (\<Sum>m \<in> ({0..<bound} - {f x}). ?ff m (insert x F)) + ?ff (f x) (insert x F)"
using sum_reord by simp
moreover hence
"(\<Sum>m\<in>{0..<bound} - {f x}. ?ff m (insert x F)) = (\<Sum>m\<in>{0..<bound} - {f x}.?ff m (insert x F))"
by simp
moreover have "?ff (f x) (insert x F) = (card (f-` {f x} \<inter>F) + 1) * g (f x)"
using insert.hyps
by simp
ultimately have
"(\<Sum>m = 0..<bound. ?ff m (insert x F))
= (\<Sum>m\<in>{0..<bound} - {f x}.(card (f -` {m} \<inter> F)) * g m) + (card (f -` {f x} \<inter>F) + 1) * g (f x)"
by simp
also have "(\<Sum>m\<in>{0..<bound} - {f x}. ?ff m F) +(card (f -` {f x} \<inter> F) + 1) * g (f x) =
(\<Sum>m\<in>{0..<bound} -{f x}.?ff m F) +?ff (f x) F + g (f x)"
using sum_vimage_proof_aux2[where n="card (f -` {f x} \<inter> F)" and r="g (f x)"]
by simp
finally have firsteq: "(\<Sum>m = 0..<bound. ?ff m (insert x F))
= (\<Sum>m\<in>{0..<bound} - {f x}. ?ff m (insert x F)) + card (f -` {f x} \<inter>
F) * g (f x) + g (f x)"
by simp
have "(\<Sum>m\<in>{0..<bound} - {f x}. card (f -` {m} \<inter> F) * g m) +
 (card (f -` {f x} \<inter> F)) * g (f x) =(\<Sum>m\<in>{0..<bound}. card (f -` {m} \<inter> F) * g m)"
using assms(1)[where w="x"] sum_reord[where h="\<lambda>m. card (f -` {m} \<inter> F) * g m"]
by simp
hence "(\<Sum>m = 0..<bound. ?ff m (insert x F)) =
(\<Sum>m\<in>{0..<bound}. ?ff m F) + g (f x)"
using firsteq
by simp
thus ?case using lefthandterm insert.hyps by simp
qed


lemma sum_vimage:
fixes g::"nat \<Rightarrow> real"
assumes bounded: "\<And>w. w \<in> H \<Longrightarrow> f w < bound" and "0 < bound"
shows "finite H \<Longrightarrow> (\<Sum>w\<in>H. g (f w)) = (\<Sum> m=0..<bound. (card ((f-`{m}) \<inter> H) ) * g m)"
(is "?fin \<Longrightarrow> ?s1 = ?s2")
proof -
let ?ff = "(\<lambda>x. if x\<in>H then f x else 0)"
let ?ss1 = "(\<Sum>w\<in>H. g (?ff w))"
have eq1: "?s1 =?ss1" by simp
let ?ss2 = "(\<Sum> m=0..<bound. (card ((?ff-`{m}) \<inter> H) ) * g m)"
have"\<And>m. ?ff -`{m} \<inter> H = f-`{m} \<inter> H" by auto
hence eq2: "?s2 = ?ss2" by simp
have boundedff: "\<And>w . ?ff w < bound" using assms by simp
hence "?fin \<Longrightarrow> ?ss1 = ?ss2"
using boundedff local.sum_vimage_proof[where H="H" and f="?ff" and bound="bound"
and g="g"] assms by simp
thus "?fin \<Longrightarrow> ?s1 = ?s2" using eq1 eq2 assms boundedff
by metis
qed


lemma finite_k_words: "finite (k_words k)" sorry

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
and bound = "Suc (k*max_len c)"]
by simp
qed

definition set_of_k_words_length_m :: "code \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> word set" where
"set_of_k_words_length_m c k m = { xk. xk \<in> k_words k} \<inter> (cw_len_concat c)-`{m}"

(*
Uses the fact that the code is an injection from k_words_length_m into m-lists
*)
lemma am_maj_aux:
assumes lossless: "lossless_code c"
shows "inj_on (fst c) ((cw_len_concat c)-`{m})" (is "inj_on ?enc ?s")
proof -
fix x y
let ?dec = "snd c"
(* assume "x \<in> ?r \<and> y \<in> ?r \<and> ?l x = ?l y" *)
have "x \<in> ?s \<and> y \<in> ?s \<and> ?enc x = ?enc y \<longrightarrow> ?dec (?enc x) = ?dec (?enc y)"
using assms lossless_code_def by auto
thus ?thesis
using inj_on_def[where f="?enc" and A="?s"]by (metis lossless lossless_code_def option.inject)
qed

lemma am_maj_aux12:
assumes lossless: "lossless_code c"
shows "finite ((fst c)`(((cw_len_concat c)-`{m}))) \<and> card ((fst c)`(((cw_len_concat c)-`{m}))) \<le> b^m"
proof -
show ?thesis sorry
qed

lemma am_maj_aux2:
assumes lossless: "lossless_code c"
shows "finite ((cw_len_concat c)-`{m}) \<and> real (card ((cw_len_concat c)-`{m})) \<le> b^m"
using assms am_maj_aux binary_space am_maj_aux12
(* sledgehammer min [e] (card_0_eq card_image card_infinite empty_subsetI
finite_Collect_le_nat finite_imageI finite_subset image_empty image_is_empty am_maj_aux am_maj_aux12 lossless) *)
(* TODO: timeout? *)
(* by (metis card_0_eq card_image card_infinite finite_imageI image_is_empty) *)
proof -
  have "\<And>x\<^sub>1 x\<^sub>2. card (fst x\<^sub>1 ` (\<lambda>R. foldr (\<lambda>R. op + (cw_len x\<^sub>1 R)) R 0) -` {x\<^sub>2}) = card ((\<lambda>R. foldr (\<lambda>R. op + (cw_len x\<^sub>1 R)) R 0) -` {x\<^sub>2}) \<or> \<not> lossless_code x\<^sub>1" using am_maj_aux card_image by blast
  thus "finite ((\<lambda>w. foldr (\<lambda>x. op + (cw_len c x)) w 0) -` {m}) \<and> real (card ((\<lambda>w. foldr (\<lambda>x. op + (cw_len c x)) w 0) -` {m})) \<le> b ^ m" by (metis am_maj_aux12 card_0_eq card_infinite finite_imageI image_is_empty lossless)
qed

lemma am_maj:
assumes lossless: "lossless_code c"
shows "card (set_of_k_words_length_m c k m)\<le> b^m" (is "?c \<le> ?b")
proof -
have "set_of_k_words_length_m c k m \<subseteq> (cw_len_concat c)-`{m}" using
set_of_k_words_length_m_def by simp
hence "card (set_of_k_words_length_m c k m) \<le> card ((cw_len_concat c)-`{m})"
using assms am_maj_aux2 Finite_Set.card_mono by blast
thus ?thesis
using assms am_maj_aux2[where c="c" and m="m" ] by simp
qed

(* let ?s="set_of_k_words_length_m c k m" and ?enc="fst c" *)

lemma empty_set_k_words:
 assumes "0 < k" and "real_code c"
 shows "set_of_k_words_length_m c k 0 = {}"
proof (rule ccontr)
assume "\<not> set_of_k_words_length_m c k 0 = {}"
hence "\<exists>x. x \<in> set_of_k_words_length_m c k 0" by auto
then obtain x where "x \<in> set_of_k_words_length_m c k 0" by auto
note x_def = this
hence "x \<in> k_words k" unfolding set_of_k_words_length_m_def by simp
hence "x \<noteq> []" using assms by auto
hence "x = hd x # tl x" by simp
moreover have
"cw_len_concat c (hd x#tl x) =  cw_len_concat c (tl x) + cw_len c (hd x)"
by (metis add.commute comp_apply foldr.simps(2))
ultimately have "cw_len_concat c x \<ge> cw_len c (hd x)" by simp
moreover have "(fst c) [(hd x)] \<noteq> []" using assms unfolding real_code_def by
simp
moreover hence "0 < cw_len c (hd x)" using cw_len_def by simp
ultimately have "0 \<noteq> cw_len_concat c x" by simp
hence "x \<notin> set_of_k_words_length_m c k 0" unfolding set_of_k_words_length_m_def
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
using binary_space by auto
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
