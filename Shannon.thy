theory Shannon
imports Information
begin
typedef bit = "{0,Suc 0}" by auto
typedef letter = "{0::nat..10}" by auto

fun alphabet :: "nat \<Rightarrow> nat set" where
  "alphabet 0 = {}"|
  "alphabet (Suc n) = {0::nat..n}"

type_synonym word = "letter list"

typedef code = "{D :: (letter list \<Rightarrow> letter list). 
D [] = [] \<and> (\<forall>x. \<forall> xs. D (x#xs) = (D [x]) @ (D xs))}"
by auto


(* 
X is the input, Y is the output.
They are not independent (if they are, all of this serves no purpose)
We fix N, N' the measures (TODO: should I? Can we have two different bit measures?)
The input is only correlated to the corresponding output.
*)
type_synonym prob = "letter \<Rightarrow> real"

locale information_space_discrete_second = information_space +
fixes Input :: "nat \<Rightarrow> ('a \<Rightarrow> letter)"
fixes Output :: "nat \<Rightarrow> ('a \<Rightarrow> letter)"
fixes fi :: "prob"
fixes fo :: "prob"
fixes N :: "'a measure" --"we should take M?"
fixes N' :: "letter measure"
fixes C :: code
(* fixes range *)
assumes distr_i:
  "simple_distributed N (Input i) fi"
assumes distr_o:
  "simple_distributed N (Output i) fo"
assumes memoryless:
"(m \<noteq> n \<longrightarrow> (indep_var N' (Input m) N' (Output n)) \<and> indep_var N' (Output m) N' (Output n))"
assumes io_corr: (* this one is useless given m_info *)
"\<not> indep_var N' (Input n) N' (Output n)"
assumes m_info:
  "\<I>(Input n ; Output n) > 0"

context information_space_discrete_second
begin
lemma un: "simple_function N (Input i)"
using distr_i simple_distributed_simple_function by blast

lemma triv: "prob {a} \<le> 1" by auto

(*
fun codelength :: "code \<Rightarrow> prob \<Rightarrow> real" where
  \<Sum>l \<in> (`space N)
*)
end
end
