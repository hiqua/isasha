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




(*
base tree, depth wanted
output : Some new tree, None if not possible to insert in this tree at this depth
We begin with a big tree with lots of possibilities
*)
fun add_to_tree :: "'z \<Rightarrow> 'z tree \<Rightarrow> nat \<Rightarrow> 'z tree option" where
  "add_to_tree e \<langle>\<rangle> _ = None"|
  "add_to_tree e t 0 = Some \<langle>\<langle>\<rangle>, e, \<langle>\<rangle>\<rangle>"|
  "add_to_tree e t (Suc d) = (
case ((add_to_tree e (left t) d),(add_to_tree e (right t) d)) of (None,None) \<Rightarrow> None
|(Some left_t,_) \<Rightarrow> Some \<langle>left_t,val t, right t\<rangle>
|(None,Some right_t) \<Rightarrow> Some \<langle>left t, val t, right_t\<rangle>
)"

(*
build a complete tree of given depth
*)
fun build_basic_tree :: "nat \<Rightarrow> int tree" where
  "build_basic_tree 0 = \<langle>\<rangle>"|
  "build_basic_tree (Suc n) = \<langle>build_basic_tree n, -1, build_basic_tree n\<rangle>"

(*
the maximal depth is by the least frequent word
*)
definition basic_tree :: "int tree" where
  "basic_tree \<equiv> build_basic_tree (li (L_enum (card L)))"


function build_tree_rec :: "nat \<Rightarrow> ('b^'n) tree \<Rightarrow> ('b^'n) tree option" where
  "build_tree_rec n cur_tree = (if Suc (card L) \<le> n
then Some cur_tree else case (add_to_tree (L_enum n) cur_tree (li (L_enum n))) of
None \<Rightarrow> None
|Some new_t \<Rightarrow> build_tree_rec (Suc n) new_t)"
by auto

fun encoding :: "'a tree \<Rightarrow> 'a \<Rightarrow> int list option" where
  "encoding \<langle>\<rangle> _ = None"|
  "encoding \<langle>\<langle>\<rangle>,v,\<langle>\<rangle>\<rangle> e = (if e = v then Some [] else None)"|
  "encoding t e = (
case (encoding (left t) e, encoding (right t) e) of
(None, None) \<Rightarrow> None
|(Some l, _) \<Rightarrow> Some (0#l)
|(_, Some l) \<Rightarrow> Some (1#l)
)
"




fun vec_number :: "'b^'n \<Rightarrow> nat set \<Rightarrow> nat" where
  "vec_number v indexes = (if L_enum_inv v \<le> Min indexes \<or> indexes = {}
then 0 else vec_number v  (indexes - {Min indexes}))"

(* when we have constructed the tree with n-1 encodings, encode the n_th element:
take the length it is supposed to have
 *)
definition max_set :: "('b^'n) set \<Rightarrow> ('b^'n) set" where
  "max_set se = {x. li x = Max (li ` se)}"


(* exists code for vectors such that code_rate \<le> H*)
lemma "\<exists>co. code_rate co X \<le> H + 1"
sorry


(* exists code for scalars such that code_rate \<le> H/n*)

end
end