theory Shannon
imports Information
begin

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
fixes source_entropy::real
assumes entropy_defi : "source_entropy = \<H>(Input 0)"

print_locale information_space

(*
TODO: generalize c::code, do not put in the locale. Have some predicates to
allow reasonings about codes. Keep the input_block_size that limits the size of the input, and use it.
*)
(* We will generalize the type "code" to any input by splitting the input in piece of length below a constant *)
subsection{* locale specific to the source coding theorem *}
locale information_space_discrete_source = information_space_discrete +
fixes input_block_size::nat
begin

definition lossless_code :: "code \<Rightarrow> bool"
where
 "lossless_code c = (\<forall>x. length x \<le> input_block_size \<longrightarrow> snd c (fst c x) = Some
 x)"

definition block_encoding_code :: "code
\<Rightarrow> bool"
where
"block_encoding_code c = (\<forall>x. length x = input_block_size \<longrightarrow> (\<forall>xs. (fst c) (x @ xs) = (fst
c) x @ (fst c) xs))"


definition real_code ::
"code \<Rightarrow> bool" where
"real_code c = (lossless_code c \<and> block_encoding_code c)"


definition code_rat :: "code \<Rightarrow> real"
where
"code_rat code = lebesgue_integral N (\<lambda>a. (fi ((Input 0) a)) * (length ((fst
code) [(Input 0) a])))"

lemma  (in information_space_discrete_source) rate_lower_bound : "source_entropy \<le> code_rate"
sorry


lemma un: "simple_function N (Input i)"
using distr_i simple_distributed_simple_function by blast

end
end
