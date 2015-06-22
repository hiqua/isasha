theory Block_Source_Code
imports Source_Code
begin
section{* Locale definition *}
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
  assumes card_L: "2 \<le> card L"

  fixes L_enum :: "nat \<Rightarrow> 'b^'n"
  assumes L_enum_bij: "bij_betw L_enum {0..card L - 1} L"
  assumes L_enum_dec: "\<And>i j. j \<in> {0..card L - 1} \<Longrightarrow> i \<le> j \<Longrightarrow>
    fi (L_enum i) \<ge> fi (L_enum j)"

  assumes fi_pos: "\<And>x. x \<in> L \<Longrightarrow> 0 < fi x"


  assumes bounded_input: "X ` space M = L"

  fixes c::"('b^'n) code"
  assumes real_code : "((\<forall>x. snd c (fst c x) = Some x) \<and>
    (\<forall>w. (fst c) w = [] \<longleftrightarrow> w = []) \<and>
    (\<forall>x. x \<noteq> [] \<longrightarrow> fst c x = (fst c) [(hd x)] @ (fst c) (tl x)))"

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
    (\<forall>x. x \<noteq> [] \<longrightarrow> fst c x = fst c [hd x] @ fst c (tl x))" using real_code by metis
qed

section{* Basics *}
context block_source_code
begin
subsection{* Direct properties and definitions from the locale *}
definition L_enum_inv :: "'b^'n \<Rightarrow> nat" where
  "L_enum_inv = the_inv_into {0..card L - 1} L_enum"

lemma L_enum_inv_inj:
  "bij_betw L_enum_inv L {0..card L - 1}" using bij_betw_the_inv_into[OF L_enum_bij]
by (simp add: L_enum_inv_def)

lemma "\<And>l. l \<in> L \<Longrightarrow> fi l \<ge> fi (L_enum (card L - 1))"
proof -
fix l
assume "l\<in>L"
from L_enum_bij obtain i where i_def: "L_enum i = l" "i\<in>{0.. card L - 1}"
by (metis L_enum_inv_def L_enum_inv_inj `l \<in> L` bij_betwE f_the_inv_into_f_bij_betw)
thus "fi l \<ge> fi (L_enum (card L - 1))" using L_enum_dec[of "card L - 1", of i] by simp
qed

lemma prb_space: "prob_space M"
using emeasure_space_1 prob_spaceI by blast

lemma fi_1: "\<And>x. x \<in> L \<Longrightarrow> fi x \<le> 1"
proof (rule ccontr)
fix x
assume asm: "x \<in> L" "\<not> fi x \<le> 1"
have "fi x \<le> (\<Sum>i\<in>L. fi i)" using fi_pos
by (smt `x \<in> L` fin_L setsum.delta' setsum_mono)
hence "1 < (\<Sum>i\<in>L. fi i)" using asm by simp
moreover have "(\<Sum>i\<in>L. fi i) = 1"
using Probability_Measure.prob_space.simple_distributed_setsum_space[OF prb_space, OF distr_i]
bounded_input by simp
ultimately show "False" by simp
qed

(* tedious, use the fact that 2 \<le> card L *)
lemma fi_11: "\<And>x. x \<in> L \<Longrightarrow> fi x < 1"
sorry

subsection{* simple lemmas about entropy *}

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


(* might be tedious *)
lemma "\<H>(X) = CARD('n) * H_i"
sorry
(*
proof -
have "\<H>(X) = - (\<Sum>x\<in>L. fi x * log b (fi x))"
using entropy_simple_distributed[OF distr_i] bounded_input by simp
*)

subsection{* Definition of li: the lengths of the future code *}

definition li::"'b^'n \<Rightarrow> nat" where
  "li x =   nat \<lceil>(log b (1/ fi x))\<rceil>"

lemma li_1: "\<And>x. x\<in>L \<Longrightarrow> 0 < log b (1/ fi x)" using fi_pos fi_11 b_val
by fastforce

lemma li_nat: "\<And>x. x\<in>L \<Longrightarrow> li x = \<lceil>(log b (1/ fi x))\<rceil>" using li_1 li_def by force

lemma li_11: "\<And>x. x\<in>L \<Longrightarrow> 1 \<le> li x" using li_1 li_nat
by (metis le_less_linear less_numeral_extra(3) less_one of_nat_0 zero_less_ceiling)

lemma li_diff_0: "li (L_enum 0) \<noteq> 0"
proof -
have "L_enum 0 \<in> L" using L_enum_bij by (simp add: bij_betwE)
hence "1 \<le> li (L_enum 0)" using li_11 by simp
thus ?thesis by simp
qed

lemma "(\<Sum>x\<in>L. b powr (-li x)) \<le> 1"
sorry

definition kraft_sum_li ::"real" where
  "kraft_sum_li = (\<Sum>l\<in>L. 1 / b ^ li l)"

definition kraft_sum_li_ineq :: "bool" where
  "kraft_sum_li_ineq = (kraft_sum_li \<le> 1)"

subsection{* Manipulation of list *}

(* main three functions to do the encoding *)
(* the lists are considered in reverse order, i.e. [0] is a prefix of [1,0] *)
fun next_list :: "bit list \<Rightarrow> bit list" where
  "next_list [] = [False]"|
  "next_list (x#xs) = (if x then False#(next_list xs) else True#xs)"

(* next_list applied n times *)
fun next_list_n :: "bit list \<Rightarrow> nat \<Rightarrow> bit list" where
  "next_list_n l 0 = l"|
  "next_list_n l (Suc n) = next_list_n (next_list l) n"

(* add n False (0) at the beginning of the list *)
fun pad :: "bit list \<Rightarrow> nat \<Rightarrow> bit list" where
  "pad l 0 = l"|
  "pad l (Suc n) = False#(pad l n)"

(* gives the nth encoding according to the lengths function *)
fun encode :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bit list" where
  "encode 0 len = pad [] (len 0)"|
  "encode (Suc n) len = pad (next_list (encode n len)) (len (Suc n) - len n)"

lemma enc_nemp: "\<And>len n. len 0 \<noteq> 0 \<Longrightarrow> encode n len \<noteq> []"
by (metis encode.elims list.distinct(1) next_list.elims pad.elims)

(* is l1 a prefix of l2
prefix in the sense of the code, suffix for the real list
 *)
inductive is_prefix :: "'z list \<Rightarrow> 'z list \<Rightarrow> bool" where
  is_pref_eq [simp, intro!]: "is_prefix l l"|
  is_pref_Cons [simp, intro!]: "is_prefix xs ys \<Longrightarrow> is_prefix xs (x#ys)"

definition is_prefix_alt::"'z list \<Rightarrow> 'z list \<Rightarrow> bool" where
  "is_prefix_alt l1 l2 \<longleftrightarrow> (\<exists>a. l2 = a@l1)"

theorems is_pref_simp = is_pref_eq is_pref_Cons

lemma "\<not> is_prefix l1 l2 \<Longrightarrow> l1 \<noteq> l2" using is_pref_eq
by auto

lemma "is_prefix l [] \<Longrightarrow> l = []" using is_prefix_def
using is_prefix.cases by blast

lemma is_pref_eq_or_tl: "is_prefix l1 l2 \<Longrightarrow> l1 = l2 \<or> is_prefix l1 (tl l2)"
by (metis is_prefix.cases list.sel(3))

lemma is_pref_tl: "is_prefix l1 l2 \<Longrightarrow> l1 \<noteq> l2 \<Longrightarrow> is_prefix l1 (tl l2)" using is_pref_eq_or_tl by auto

lemma is_pref_len: "is_prefix l1 l2 \<Longrightarrow> length l1 \<le> length l2" by (induct rule:is_prefix.induct[OF assms]) auto

lemma len_not_is_pref: "length l2 < length l1 \<Longrightarrow> \<not>is_prefix l1 l2" using is_pref_len using not_less by auto

lemma
assumes "is_prefix l1 l2" "length l1 = length l2"
shows "l1 = l2"
proof (cases l2)
case Nil
thus ?thesis using assms by simp
next
case Cons
show ?thesis
proof (rule ccontr)
assume "l1 \<noteq> l2"
have "l2 = hd l2 # tl l2" using Cons by simp
hence "length (tl l2) < length l2" by (metis impossible_Cons le_less_linear)
hence "length (tl l2) < length l1" using assms by simp
moreover from assms `l1 \<noteq> l2` have "is_prefix l1 (tl l2)" using is_pref_tl by auto
ultimately show False using len_not_is_pref by blast
qed
qed

lemma "is_prefix l1 l2 \<Longrightarrow> (\<exists>a. l2 = a @ l1)"
proof (induct rule: is_prefix.induct)
show "\<And>l. \<exists>a. l = a @ l" by simp
fix xs::"'z list"
fix ys x
assume "is_prefix xs ys" "\<exists>a. ys = a @ xs"
then obtain a where "ys = a @ xs" by auto
hence "x#ys = (x#a)@xs" by simp
thus "\<exists>a. x # ys = a @ xs" by simp
qed

lemma
assumes pref: "is_prefix l1 l2" "is_prefix l3 l2" "length l1 \<le> length l3"
shows "is_prefix l1 l3"
using pref
sorry


lemma "x@xr = y@yr \<Longrightarrow> length xr \<le> length yr \<Longrightarrow> is_prefix xr yr" using is_pref_simp
sorry

lemma "\<And>l. length (next_list l) = length l"
(* easy *)
sorry

subsection{* Ordering lists used in Huffman *}
subsubsection{* Order definition *}
definition less_eq :: "bit list \<Rightarrow> bit list \<Rightarrow> bool" (infix "\<preceq>" 50) where
  "less_eq l1 l2 = (\<exists>n. l2 = next_list_n l1 n)"

definition less :: "bit list \<Rightarrow> bit list \<Rightarrow> bool" (infix "\<prec>" 50) where
  "l1 \<prec> l2 = (l1 \<preceq> l2 \<and> l1 \<noteq> l2)"

(* easy, how to use?
just use lemmas from orderings.thy
*)
interpretation ordering less_eq less
sorry

(* example using this interpretation *)
lemma "less_eq l1 l2 \<longleftrightarrow> less l1 l2 \<or> l1 = l2"
by (simp add: order_iff_strict)

subsubsection{* Custom lemmas *}
(* ? *)

section{* Huffman Encoding *}
definition huffman_encoding_u :: "('b^'n) \<Rightarrow> bit list" where
  "huffman_encoding_u v = encode (L_enum_inv v) (\<lambda>n. li (L_enum n))"

lemma huffman_encoding_u_nemp: "len 0 \<noteq> 0 \<longrightarrow> v\<in>L \<longrightarrow> huffman_encoding_u v \<noteq> []"
using enc_nemp[of "\<lambda>n. li (L_enum n)",of "L_enum_inv v"]
huffman_encoding_u_def li_11 L_enum_inv_inj sorry

definition huffman_lists :: "bit list set" where
  "huffman_lists = huffman_encoding_u ` L"

(* hard *)
lemma
assumes kraft_sum_li_ineq
shows "\<And>i j. j < card L \<Longrightarrow> i < j \<Longrightarrow> (huffman_encoding (L_enum i) \<prec> huffman_encoding (L_enum j))"
sorry

lemma "l1 \<prec> l2 \<Longrightarrow> \<not> is_prefix l1 l2"
sorry

theorem
assumes kraft_sum_li_ineq
shows "\<And>a b. a\<in>L \<Longrightarrow> b\<in>L \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<not> is_prefix (huffman_encoding_u a) (huffman_encoding_u b)"
sorry

(* easy? *)
lemma "\<And>l. l\<in>L \<Longrightarrow> length (huffman_encoding_u l) = li l"
sorry

(* easy *)
lemma encoding_inj: "inj_on huffman_encoding_u L"
sorry

lemma "bij_betw huffman_encoding_u L (huffman_encoding_u`L)"
using inj_on_imp_bij_betw[OF encoding_inj] by simp


(* TODO: remove these definitions of the inverse, and use injections instead *)
definition huffman_encoding_reverse_u :: "bit list \<Rightarrow> ('b^'n) option" where
  "huffman_encoding_reverse_u x = (if x \<in> (huffman_encoding_u ` L) then Some (the_inv_into L huffman_encoding_u x) else None)"

fun huffman_encoding_reverse_aux :: "bit list \<Rightarrow> bit list \<Rightarrow> ('b^'n) list option" where
  "huffman_encoding_reverse_aux xs [] = (case huffman_encoding_reverse_u xs of None \<Rightarrow> None
|Some res \<Rightarrow> (Some [res]))"|
  "huffman_encoding_reverse_aux xs (y#ys) = (case huffman_encoding_reverse_u xs
of None \<Rightarrow>
huffman_encoding_reverse_aux (xs @ [y]) ys
|Some res \<Rightarrow> (case huffman_encoding_reverse_aux [] ys
  of None \<Rightarrow> None
|Some res2 \<Rightarrow> Some (res # res2))
)"

definition huffman_decoding :: "bit list \<Rightarrow> ('b^'n) list option" where
  "huffman_decoding xs = huffman_encoding_reverse_aux [] xs"

definition huffman_encoding :: "('b^'n) list \<Rightarrow> bit list" where
  huffman_encoding_def: "huffman_encoding xs = (fold (\<lambda>vl res. (huffman_encoding_u vl) @ res) xs [])"

definition huffman_encoding_alt :: "('b^'n) list \<Rightarrow> bit list" where
  huffman_encoding_alt_def: "huffman_encoding_alt x = concat (map huffman_encoding_u x)"

(* the set of possible inputs *)
definition valid_input_set :: "('b^'n) list set" where
  "valid_input_set = {w. real_word w}"

lemma "x#xs \<in> valid_input_set \<Longrightarrow> xs \<in> valid_input_set"
using valid_input_set_def by auto

lemma huff_nemp: "x \<in> L \<Longrightarrow> huffman_encoding_alt (x#xs) \<noteq> []"
proof -
  have "x\<in>L \<Longrightarrow> huffman_encoding_u x \<noteq> []"
  using huffman_encoding_u_nemp by auto
  thus "x \<in> L \<Longrightarrow> huffman_encoding_alt (x#xs) \<noteq> []" using huffman_encoding_alt_def by simp
qed

lemma huff_emp_1: "real_word x \<Longrightarrow> (huffman_encoding_alt x = [] \<longrightarrow> x = [])"
proof
show "real_word x \<Longrightarrow> huffman_encoding_alt x = [] \<Longrightarrow> x = []"
  proof (rule ccontr)
    assume asm: "real_word x" "huffman_encoding_alt x = []" "x \<noteq> []"
    hence "x = (hd x) # tl x" by simp
    hence "huffman_encoding_alt x = huffman_encoding_u (hd x) @ concat (map huffman_encoding_u (tl x))"
    using huffman_encoding_alt_def by (metis List.bind_def bind_simps(2))
    moreover have in_L: "hd x \<in> L" using asm by auto
    hence "huffman_encoding_alt x \<noteq> []" using huffman_encoding_alt_def huff_nemp[OF in_L]
    using calculation by auto
    thus False using asm by simp
  qed
qed

lemma huff_emp_2: "huffman_encoding_alt [] = []" using huffman_encoding_alt_def by simp

theorems huff_emp = huff_emp_1 huff_emp_2

(*
lemma "x \<noteq> [] \<Longrightarrow> huffman_encoding_alt x = huffman_encoding_alt (tl x) @ huffman_encoding_u (hd x)"
using huffman_encoding_def fold_Cons
proof -
let ?f = "\<lambda>vl res. (huffman_encoding_u vl) @ res"
fix x::"('b,'n) vec list"
assume "x \<noteq> []"
hence nemp: "x = hd x # tl x" by simp
hence "huffman_encoding x = (fold ?f x [])"
using huffman_encoding_def by simp
hence "huffman_encoding x = (fold ?f (hd x#tl x) [])"
using nemp by simp
also have "\<dots> = (fold ?f (tl x) \<circ> ?f (hd x)) []" using fold_Cons by simp
also have "\<dots> = (fold ?f (tl x)) ((?f (hd x)) [])" by simp
also have "\<dots> = (fold ?f (tl x)) (huffman_encoding_u (hd x))" by simp
also have "\<dots> = huffman_encoding (tl x) @ huffman_encoding_u (hd x)" using huffman_encoding_def
*)

lemma rw_hd: "real_word (x#xs) \<Longrightarrow> x \<in> L" by simp

(* using prefix properties *)
(* theorem "inj_on huffman_encoding valid_input_set" *)
theorem huffman_encoding_inj:
"real_word x \<Longrightarrow> real_word y \<Longrightarrow> huffman_encoding_alt x = huffman_encoding_alt y \<Longrightarrow> x = y"
proof (induction x arbitrary: y)
case Nil
hence "huffman_encoding_alt y = []" sorry
hence "y = []" sorry
thus ?case by simp
next
case (Cons xh xt)
have "y \<noteq> []" using huff_nemp Cons huff_emp rw_hd by auto
hence "y = hd y # tl y" by simp
hence "huffman_encoding_alt y = huffman_encoding_u (hd y) @ huffman_encoding_alt (tl y)"
by (metis concat.simps(2) huffman_encoding_alt_def list.simps(9))
have "xh # xt = y" sorry
thus ?case by simp

oops
(*
using encoding_inj huffman_encoding_def sorry

qed
thus "inj_on huffman_encoding valid_input_set" by (simp add: inj_on_def)
qed
oops
*)

definition huffman_decoding_alt :: "bit list \<Rightarrow> ('b^'n) list" where
  "huffman_decoding_alt xs = the_inv_into valid_input_set huffman_encoding xs"

(* define the associated code *)
definition huffman_code :: "('b^'n) code" where
  "huffman_code = (huffman_encoding, huffman_decoding)"

section{* Proofs: it is a real code that respect certain properties *}
subsection{* lemmas on lists *}
lemma "\<And>l. True \<in> set l \<Longrightarrow> l \<noteq> next_list l"
by (metis length_greater_0_conv length_pos_if_in_set list.inject next_list.elims)

lemma "length (pad l n) = length l + n"
proof (induction n)
case 0
show "length (pad l 0) = length l + 0" by simp
case (Suc m)
have "length (pad l (Suc m)) = length (pad l m) + 1" by simp
thus ?case using Suc by simp
qed

lemma "\<And>l. next_list l \<noteq> l"
by (metis (full_types) list.sel(1) next_list.elims not_Cons_self2)

subsection{* The Huffman code is a real code *}

(* really tedious to prove, I should only prove that huffman_encoding is injective on a set of lists,
*)
lemma "set x \<subseteq> L \<Longrightarrow> huffman_decoding (huffman_encoding x) = Some x"
sorry

lemma "set x \<subseteq> L \<Longrightarrow> huffman_encoding x = [] \<longleftrightarrow> x = []"
using enc_nemp huffman_encoding_def sorry

lemma "x \<noteq> [] \<Longrightarrow> huffman_encoding x = huffman_encoding_u (hd x) @ (huffman_encoding (tl x))"
(* using huffman_encoding_def huffman_encoding_u_def *) unfolding huffman_encoding_def
using fold_Cons
fold_simps sorry


(* theorem huff_real_code = three previous lemmas *)


(* Main theorem: find the average length of this code *)
theorem "code_rate huffman_code X \<le> \<H>(X) + 1"
sorry

end
end
