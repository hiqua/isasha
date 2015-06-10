theory Block_Source_Code
imports Source_Code "~~/src/HOL/Library/Tree"
begin
locale block_source_code = information_space +
  fixes fi :: "'b^'n \<Rightarrow> real"
  fixes X::"'a \<Rightarrow> ('b^'n)"
  assumes distr_i: "simple_distributed M X fi"
  fixes H::real
  assumes b_val: "b = 2"
  assumes entropy_defi: "H = \<H>(X)"

  fixes L :: "('b^'n) set"
  assumes fin_L: "finite L"
  assumes emp_L: "L \<noteq> {}"

  fixes L_enum :: "nat \<Rightarrow> 'b^'n"
  assumes L_enum_bij: "bij_betw L_enum {1..card L} L"
  assumes L_enum_dec: "\<And>i j. i\<in>{1..card L} \<Longrightarrow> j\<in>{1..card L} \<Longrightarrow> i \<le> j \<Longrightarrow>
    fi (L_enum i) \<ge> fi (L_enum j)"

    assumes fi_pos: "\<And>x. x \<in> L \<Longrightarrow> 0 < fi x"


  assumes bounded_input: "X ` space M = L"

  fixes c::"('b^'n) code"
  assumes real_code : "((\<forall>x. snd c (fst c x) = Some x) \<and>
    (\<forall>w. (fst c) w = [] \<longleftrightarrow> w = []) \<and>
    (\<forall>x. fst c x = (fst c) [(hd x)] @ (fst c) (tl x)))"

  (* distribution according a law *)
  fixes f:: "'b \<Rightarrow> real"
  assumes distr_comp: "\<And>i. simple_distributed M (\<lambda>a. (X a)$i) f"
  (* independence *)
  assumes indep: "\<forall>x. fi x = (\<Prod>i\<in>UNIV. f (x$i))"
  fixes H_i::real
  assumes H_i_def: "\<exists>i. H_i = \<H>(\<lambda>a. (X a)$i)"
  fixes S
  assumes space_img_1: "\<And>i. (\<lambda>a. (X a)$i) ` space M = S"
  assumes L_S_eq: "L = {v. \<forall>i. v$i \<in> S}"

print_locale information_space
print_locale source_code


sublocale block_source_code \<subseteq> source_code

proof
show "simple_distributed M X fi" by (simp add: distr_i)
show "b = 2" by (simp add: b_val)
show "H = \<H>(X)" by (simp add: entropy_defi)
show "finite L" by (simp add: fin_L)
show "L \<noteq> {}" by (simp add: emp_L)
show "X ` space M = L" by (simp add: bounded_input)
show "(\<forall>x. snd c (fst c x) = Some x) \<and>
    (\<forall>w. (fst c w = []) = (w = [])) \<and>
    (\<forall>x. fst c x = fst c [hd x] @ fst c (tl x))" using real_code by metis
qed


context block_source_code
begin
lemma "H \<le> cr" using rate_lower_bound by simp


(* INTERESTING: not the same to have this def, and X_i i a = X a $ i *)
definition X_i::"'n \<Rightarrow> 'a \<Rightarrow> 'b" where
  "X_i i = (\<lambda>a. X a $ i)"

lemma space_img_2: "\<And>i. X_i i ` space M = S"
by (simp add: space_img_1 X_i_def image_cong)

theorems space_img = space_img_1 space_img_2

lemma entropy_sum: "\<And>i. \<H>(X_i i) = - (\<Sum>x\<in>(X_i i)`space M. f x * log b (f x))"
proof -
fix i
have "(\<lambda>a. X a $ i) =(X_i i)" using X_i_def[of i] by auto
moreover hence "\<H>(\<lambda>a. X a $ i) = \<H>(X_i i)" by simp
moreover have "\<H>(\<lambda>a. X a $ i) = - (\<Sum>x\<in>(\<lambda>a. X a $ i)`space M. f x * log b (f x))"
using entropy_simple_distributed[OF distr_comp] by simp
ultimately show "\<H>(X_i i) = - (\<Sum>x\<in>(X_i i)`space M. f x * log b (f x))" by simp
qed

lemma entropy_sum_2: "\<And>i. \<H>(X_i i) = - (\<Sum>x\<in>S. f x * log b (f x ))"
using entropy_sum space_img by simp

lemma entropy_forall: "\<And>i j. \<H>(X_i i) = \<H>(X_i j)"
using entropy_sum space_img
proof -
fix i j
show " \<H>(X_i i) = \<H>(X_i j)"
using entropy_sum space_img
by simp
qed

lemma "\<And>i. H_i = \<H>(X_i i)"
proof -
fix i
from H_i_def obtain j where "H_i = \<H>(\<lambda>a. X a $ j)" by blast
hence "H_i = \<H>(X_i j)" using X_i_def by simp
moreover have "\<H>(X_i j) = \<H>(X_i i)" using entropy_forall by simp
ultimately show "H_i = \<H>(X_i i)" by simp
qed


lemma "\<H>(X) = CARD('n) * H_i"
sorry
(*
proof -
have "\<H>(X) = - (\<Sum>x\<in>L. fi x * log b (fi x))"
using entropy_simple_distributed[OF distr_i] bounded_input by simp
*)

subsection{* Construct a code complying with the upper bound *}

definition llll::"int tree" where
  "llll = Leaf"

definition li::"'b^'n \<Rightarrow> nat" where
  "li x =   nat \<lceil>(log b (1/ fi x))\<rceil>"

lemma "\<And>x. x\<in>L \<Longrightarrow> li x = \<lceil>(log b (1/ fi x))\<rceil>"
sorry


print_context
print_locale block_source_code

lemma prb_space: "prob_space M"
using emeasure_space_1 prob_spaceI by blast


lemma (in block_source_code) "\<And>x. x \<in> L \<Longrightarrow> fi x \<le> 1"
using bounded_input Probability_Measure.prob_space.simple_distributed_setsum_space[OF prb_space, OF distr_i] fi_pos


sorry

lemma "\<And>x. x\<in> L \<Longrightarrow> 0 \<le> li x"
using li_def fi_pos distr_i bounded_input
sorry

lemma "(\<Sum>x\<in>L. b powr (-li x)) \<le> 1"
sorry


(* define  function n_th_order that for an integer n from 1 to card S give the nth element with the
order given by a certain function (the probability to occur, namely)
*)
(* done: L_enum *)

definition L_enum_inv :: "'b^'n \<Rightarrow> nat" where
  "L_enum_inv = the_inv_into {1..card L} L_enum"

lemma L_enum_inv_inj:
  "bij_betw L_enum_inv L {1..card L}" using bij_betw_the_inv_into[OF L_enum_bij]
by (simp add: L_enum_inv_def)

lemma "\<And>l. l \<in> L \<Longrightarrow> li l \<le> li (L_enum (card L))"
sorry

definition kraft_sum_li ::"real" where
  "kraft_sum_li = (\<Sum>l\<in>L. 1 / b ^ li l)"






(* fun huffman_encoding :: "('b^'n) \<Rightarrow> nat list" where *)


(* medium because of option tricks *)
lemma "\<And>l. l\<in>L \<Longrightarrow> length (huffman_encoding l) = li l"
sorry


lemma encoding_inj: "inj_on huffman_encoding L"
sorry

lemma "bij_betw huffman_encoding L (huffman_encoding`L)"
using inj_on_imp_bij_betw[OF encoding_inj] by simp

(* lemma exists the inverse function *)

(* define the associated code *)



(* exists code for vectors such that code_rate \<le> H*)
lemma "\<exists>co. code_rate co X \<le> H + 1"
sorry


(* exists code for scalars such that code_rate \<le> H/n*)

end
end