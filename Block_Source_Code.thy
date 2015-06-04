theory Block_Source_Code
imports Source_Code
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


lemma "\<forall>i. \<H>(X) = CARD('n) * H_i"
using indep
sorry


(* exists code for vectors such that code_rate \<le> H*)
lemma "\<exists>co. code_rate co X \<le> H + 1"
sorry


(* exists code for scalars such that code_rate \<le> H/n*)

end
end