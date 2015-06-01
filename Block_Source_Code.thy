theory Block_Source_Code
imports Source_Code
begin
locale block_source_code = information_space +
  fixes fi :: "'b list \<Rightarrow> real"
  fixes X::"'a \<Rightarrow> 'b list"
  assumes distr_i: "simple_distributed M X fi"
  fixes H::real
  assumes b_val: "b = 2"
  assumes entropy_defi: "H = \<H>(X)"

  fixes L :: "'b list set"
  assumes fin_L: "finite L"
  assumes emp_L: "L \<noteq> {}"

  assumes bounded_input: "X ` space M = L"
  
  fixes c::"'b list code"
  assumes real_code : "((\<forall>x. snd c (fst c x) = Some x) \<and>
(\<forall>w. (fst c) w = [] \<longleftrightarrow> w = []) \<and>
(\<forall>x. fst c x = (fst c) [(hd x)] @ (fst c) (tl x)))"

  fixes max_index::nat
  assumes L_len: "\<And>x. x\<in>L \<Longrightarrow> length x = Suc max_index"


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
definition X_th :: "nat \<Rightarrow> 'a \<Rightarrow> 'b" where
  "X_th n a = (X a) ! n"



end

locale block_source_code_link = block_source_code +
  fixes L_u
  assumes "L = {w. set w \<subseteq> L_u}"
  fixes f
  assumes "\<And>n. n \<le> max_index \<Longrightarrow> simple_distributed M (X_th n) f"
begin
lemma "\<And>bl. bl \<in> L \<Longrightarrow> fi bl = (\<Prod>i\<in>{1::nat..n}. f (bl!i))"
sorry


lemma "\<H>(X) = Suc(max_index) * \<H>(X_th 0)"
sorry

lemma
  fixes lengths::"'b \<Rightarrow> nat"
  fixes letters::"'b set"
  assumes fin_letters: "finite letters"
  assumes kraft_ineq: "(\<Sum>i\<in>letters. 1/ b^(lengths i)) \<le> 1"
  shows "\<exists>g::'b code. \<forall>x. x\<in> letters \<longrightarrow> length (fst g [x]) = lengths x \<and> inj_on (fst g) ((\<lambda>x. [x]) ` letters)"
sorry

lemma
  shows "\<exists>g::'b code.

end
end