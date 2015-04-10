theory Shannon
imports Information
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
assumes bounded_input: "fi input_bound \<noteq> 0 \<and> (input_bound \<le> n \<longrightarrow> fi n = 0)"

print_locale information_space

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

definition block_encoding_code :: "code\<Rightarrow> bool" where
"block_encoding_code c = (\<forall>x. length x = input_block_size \<longrightarrow> (\<forall>xs. (fst c) (x @ xs) = (fst
c) x @ (fst c) xs))"

definition real_code ::"code \<Rightarrow> bool" where
"real_code c = (lossless_code c \<and> block_encoding_code c)"

(*
The code rate is the expectation of the length of the code taken on all inputs.
*)
definition code_rate :: "code \<Rightarrow> real" where
"code_rate code = lebesgue_integral N (\<lambda>a. (fi ((Input 0) a)) * (length ((fst
code) [(Input 0) a])))"

definition cw_len :: "code \<Rightarrow> word \<Rightarrow> nat" where
  "cw_len c w = length ((fst c) w)"

definition cw_lens :: "code \<Rightarrow> nat set" where
  "cw_lens c = (\<lambda>x. cw_len c (x#[])) ` {n. n \<le> input_bound}"

 definition max_len :: "code \<Rightarrow> nat" where
  "max_len c = Max (cw_lens c)"

definition kraft_sum :: "code \<Rightarrow> real" where
  "kraft_sum c = (\<Sum>i\<in>(cw_lens c). 1 / (b^i))"

definition kraft_inequality :: "code \<Rightarrow> bool" where
  "kraft_inequality c = (kraft_sum c \<le> 1)"

fun dumm :: "nat \<Rightarrow> nat" where
  "dumm 0 = 1"|
  "dumm (Suc n) = 3"

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
