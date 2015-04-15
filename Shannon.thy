theory Shannon
imports Information Finite_Set
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
assumes "letters = {0..<input_bound}"
assumes bounded_input: "fi input_bound \<noteq> 0 \<and> (input_bound \<le> n \<longrightarrow> fi n = 0)"

print_locale information_space_discrete

(*
TODO: Have some predicates to
allow reasonings about codes. Keep the input_block_size that limits the size of the input, and use it.
*)
(* We will generalize the type "code" to any input by splitting the input in piece of length below a constant *)
subsection{* locale specific to the source coding theorem *}
locale information_space_discrete_source = information_space_discrete +
fixes input_block_size::nat
begin

definition lossless_code :: "code \<Rightarrow> bool" where
"lossless_code c = (\<forall>x. length x \<le> input_block_size \<longrightarrow> snd c (fst c x) = Some
x)"

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

definition k_words :: "nat \<Rightarrow> word set" where
  "k_words k = {w. length w = k}"

(*
Is the code a real source encoding code?
_lossless
_uniquely decodable
*)
definition real_code ::"code \<Rightarrow> bool" where
"real_code c = (lossless_code c)"

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

fun cw_len_concat :: "code \<Rightarrow> word \<Rightarrow> nat" where
  "cw_len_concat c [] = 0" |
  "cw_len_concat c (x#xs) = cw_len c x + cw_len_concat c xs"

 definition max_len :: "code \<Rightarrow> nat" where
  "max_len c = Max ((\<lambda>x. cw_len c x) ` {n. n \<le> input_bound})"

definition kraft_sum :: "code \<Rightarrow> real" where
  "kraft_sum c = (\<Sum>i\<in>letters. 1 / b^(cw_len c i))"

definition kraft_inequality :: "code \<Rightarrow> bool" where
  "kraft_inequality c = (kraft_sum c \<le> 1)"

lemma kraft_sum_power :
  "(kraft_sum c) ^k = (\<Sum>w \<in> (k_words k). 1 / b^(cw_len_concat c w))"
proof sorry

lemma max_len_concat :
  "\<forall>w. w\<in> (k_words k) \<Longrightarrow> cw_len_concat c w \<le> k * max_len c"
proof sorry

definition set_of_k_words_length_m :: "code \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> word set" where
  (* "set_of_k_words_length_m c k m = { xk. xk \<in> k_words k \<and> cw_len_concat c xk =
   m}" *)
"set_of_k_words_length_m c k m = { xk. xk \<in> k_words k} \<inter> (cw_len_concat c)-`{m}"

lemma bound_len_concat:
  "w \<in> k_words k \<Longrightarrow> cw_len_concat c w \<le> k * max_len c"
proof sorry

(*
g i = 1/b^i
f  = cw_len_concat c
*)
lemma sum_vimage:
  fixes f::"nat list \<Rightarrow>nat"
  fixes g::"nat \<Rightarrow> real"
  fixes H
  fixes bound
  assumes bounded: "w \<in> H \<Longrightarrow> f w < bound"
  shows "finite H \<Longrightarrow> (\<Sum>w\<in>H. g (f w)) = (\<Sum> m=1..<bound. (card ((f-`{m}) \<inter> H))* g m)"
proof sorry


(*
5.54
*)
lemma kraft_sum_rewrite :
fixes k
fixes c
  assumes "k \<noteq> 0"
  shows "(\<Sum>w \<in> (k_words k). 1 / b^(cw_len_concat c w)) =
(\<Sum>m=1..<Suc (k*max_len c). card (k_words k \<inter> ((cw_len_concat c) -` {m})) * (1 /
b^m))" (is "?L = ?R")
proof -
have "w \<in> k_words k \<Longrightarrow> cw_len_concat c w \<le> k * max_len c"
using bound_len_concat by simp
then have "w \<in> k_words k \<Longrightarrow> cw_len_concat c w < Suc ( k * max_len c)" by auto
moreover have "finite (k_words k)" sorry
 (* by (metis bounded_input order_refl) *)
moreover have "?R = (\<Sum>m = 1..<Suc (k * max_len c). real (
card (cw_len_concat c -` {m} \<inter> k_words k)) * (1 / b ^ m)
)"
using Set.Int_commute[where A ="k_words k"] by auto
ultimately show ?thesis using  Set.Int_commute[where A ="cw_len_concat c -` {m}"] sum_vimage[where f=
"cw_len_concat c" and g = "(\<lambda>i. 1/ (b^i))" and H ="k_words k" and bound = "Suc
(k*max_len c)"] by metis
qed

lemma am_maj :
  "card (set_of_k_words_length_m c k m) \<le> b^m"
proof sorry


lemma kraft_sum_rewrite2:
fixes c
assumes "0 < max_len c"
shows "real (\<Sum>m=1..<Suc (k*max_len c). real (card (set_of_k_words_length_m c k m))  / b^m) \<le> real (k * max_len c)"
proof -
have 0: "(\<Sum>m=1..<Suc (k*max_len c). (card (set_of_k_words_length_m c k m) / b^m)) \<le> (\<Sum>m=1..<Suc(k * max_len c). b^m / b^m)"
using am_maj
(* from try *)
proof -
  have "\<And>x\<^sub>5 u. (\<Sum>R = Suc 0..<Suc 0. real_of_nat (card {Ra \<in> k_words 0. cw_len_concat x\<^sub>5 Ra = R})) / b ^ u = (\<Sum>R\<in>k_words 0. 1 / b ^ cw_len_concat x\<^sub>5 R)" by (metis (no_types) One_nat_def kraft_sum_rewrite mult_zero_left real_of_nat_def real_of_nat_setsum)
  thus "(\<Sum>m = 1..<Suc (k * max_len c). real (card (set_of_k_words_length_m c k m)) / b ^ m) \<le> (\<Sum>m = 1..<Suc (k * max_len c). b ^ m / b ^ m)" by (metis (no_types) divide_zero_left kraft_sum_power one_neq_zero power_0 setsum_op_ivl_Suc zero_less_Suc)
qed
have 1: "(\<Sum>m=1..<Suc(k * max_len c). b^m / b^m) = (\<Sum>m=1..<Suc(k
*max_len c). 1)" using binary_space by auto
 have 2: "(\<Sum>m=1..<Suc(k*max_len c). 1) =  (k * max_len c)" using assms by simp
from 0 1 2 show ?thesis
(*from try *)
proof -
  have "\<And>u w x. real_of_nat (\<Sum>uub = 1..<Suc (u * max_len w). card {uuc \<in> k_words u. cw_len_concat w uuc = uub}) / b ^ x = kraft_sum w ^ u" using kraft_sum_power kraft_sum_rewrite real_of_nat_def by auto
  hence "\<And>w. real_of_nat (\<Sum>uub = 1..<1. card {uuc \<in> k_words 0. cw_len_concat w uuc = uub}) = 1" by (metis (no_types) One_nat_def divide_divide_eq_right monoid_mult_class.mult.right_neutral mult_zero_left power_0 times_divide_eq_right)
  thus "real (\<Sum>m = 1..<Suc (k * max_len c). real (card (set_of_k_words_length_m c k m)) / b ^ m) \<le> real (k * max_len c)" by simp
qed
qed

lemma kraft_sum_power_bound :
  fixes c
  assumes "0 < max_len c"
  shows "(kraft_sum c)^k \<le> real (k * max_len c)"
proof -
show ?thesis using kraft_sum_power kraft_sum_rewrite kraft_sum_rewrite2





lemma partition:
  assumes bounded: "\<forall>x \<in> H. f x < (Suc m::nat)"
  shows "finite H \<Longrightarrow> H = (\<Union>i \<in> {0..m}. ( H\<inter>f-`{i}))" using bounded by auto

(* lemma partition_sum: *)

lemma sum_transform_aux:
  assumes bounded: "\<forall>x \<in> H. f x < (Suc m::nat)"
  shows "finite H \<Longrightarrow> (\<Sum>x\<in>H\<inter>f-`{i}.f x) = i * card (f-`{i} \<inter> H)"
proof auto
assume "finite H"
hence "card (H \<inter> (f -` {i})) = card ((f -` {i}) \<inter> H)"
using Set.Int_commute[where A=H]
by simp
thus "finite H \<Longrightarrow> card (H \<inter> f -` {i}) \<noteq> card (f -` {i} \<inter> H) \<Longrightarrow> i = 0"
by auto
qed



lemma sum_transform_aux2:
  shows "finite H \<Longrightarrow>(\<Sum>x\<in>H\<inter>{x. f x < Suc m} . f x) = (\<Sum>i=0..<(Suc m) .
  (\<Sum>x\<in>H\<inter>f-`{i}.f x))"
proof sorry

(*
proof (induct m)
case 0 then show ?case  using  sum_transform_aux by auto
next
case (Suc n)
then have recur_right: "(\<Sum>i = 0..<Suc (Suc m). setsum f (H \<inter> f -` {i})) = (\<Sum>i = 0..< (Suc m).
setsum f (H \<inter> f -` {i})) + setsum f (H\<inter>f-`{Suc m})"
by auto
*)



lemma sum_transform:
  assumes bounded: "\<forall>x \<in> H. f x < m"
  shows "finite H \<Longrightarrow> (\<Sum>x\<in>H. f x) = (\<Sum> i=0..<m. (i * card ((f-`{i}) \<inter> H)))"
proof (induct  rule: finite_induct)
case empty
thus ?case by simp
next
  case (insert x F)
  have first_case: "f x \<noteq> i \<Longrightarrow>  card (f -` {i} \<inter> insert x F) =  card (f -` {i} \<inter> F)"
  by auto
  have "\<lbrakk>f x = i ; \<not>x \<in> F \<rbrakk>  \<Longrightarrow>
(f -` {i} \<inter> insert x F) =  (f -`  {i} \<inter> F) \<union> {x} "
  by auto
  hence second_case: "\<lbrakk>f x = i ; \<not>x \<in> F \<rbrakk>  \<Longrightarrow>
  card (f -` {i} \<inter> insert x F) =  card (f -`  {i} \<inter> F) + 1"
by (metis (erased, hide_lams) Int_iff One_nat_def Un_commute add.commute add_Suc card_insert_disjoint finite_Int insert.hyps(1) insert_is_Un monoid_add_class.add.left_neutral)
  from second_case
  have second_case_imp :  "\<lbrakk>f x = i ; \<not>x \<in> F \<rbrakk>  \<Longrightarrow>
  i*card (f -` {i} \<inter> insert x F) =  i * card (f -`  {i} \<inter> F) + i"
  by auto

  have "finite F \<Longrightarrow> \<not>x\<in>F \<Longrightarrow> (\<Sum>y \<in> (insert x F). f y) = ((\<Sum>y \<in> F. f y) + f x)"
  by auto

  assume "finite F" "\<not>x\<in>F"
  have  "(\<Sum>i = 0..<m. i * card (f -` {i} \<inter> insert x F)) =  (\<Sum>i = 0..<m. i * card
  (f -` {i} \<inter> F) + f x)" using first_case second_case_imp sorry
  thus ?case by simp
 qed



(*
lemma sum_power : "finite A \<Rightarrow> (\<Sum>x\<in>A.x)^k = \<Sum>x\<in>(A^k). x "
*)
lemma kraft_sum_power_k :
  assumes "real_code c"
  shows "kraft_sum c ^ k \<le> k * max_len c"
sorry

theorem McMillan : "real_code c \<Longrightarrow> kraft_inequality c"
sorry

(*
_Kraft inequality for uniquely decodable codes using the McMillan theorem
*)
theorem rate_lower_bound : "real_code c \<Longrightarrow> source_entropy \<le> code_rate c"
sorry

theorem kraft_theorem :
  assumes "(\<Sum> k\<in>{0..< input_bound}. (1 / b^(lengthk k))) \<le> 1"
  shows "\<exists>c. real_code c \<and> (k\<in>{0..<input_bound} \<longrightarrow> cw_len c [k] = lengthk k)"
sorry

theorem rate_upper_bound : "0 < \<epsilon> \<Longrightarrow> (\<exists>n. \<exists>c. n \<le> input_block_size \<Longrightarrow> (real_code c
\<and> code_rate c \<le> source_entropy + \<epsilon>))"
sorry

end
end
