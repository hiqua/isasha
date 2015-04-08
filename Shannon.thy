theory Shannon
imports Information "~~/src/HOL/Word/Word"
begin
(* typedef dbit = "{0::nat, 1, 2}" by auto*)
typedef bit = "{True,False}" by auto
datatype dbit = B bit | D

(*typedef letter = "{0::nat..9}" by auto*)
type_synonym letter = nat
typedef ll = "{0::nat..<10}"
by (metis atLeastLessThan_iff le0 zero_less_numeral)


(*
Definition of the class of coded types, that is, types for which there is an
encoding and decoding function.
We assign a length to our type, this will be the length of the words we consider
(constant).
In practice, 'a will represent a D-ary alphabet, i.e. a finite set.
For now, there are only guarantees of well-defined functions if the sizes
match.
What if they don't?
*)

class coded = len +
fixes enc :: "'a list \<Rightarrow> bit list"
fixes dec :: "bit list \<Rightarrow> 'a list"
assumes "\<forall>x. (length x) = len_of TYPE ('a) \<Longrightarrow>  dec (enc x) = x"

class block_coded = coded +
fixes block_enc :: "'a list \<Rightarrow> bit list"
fixes block_dec :: "bit list \<Rightarrow> 'a list"
assumes "\<forall>x.\<forall>xs. (length x) = len_of TYPE('a) \<Longrightarrow>
block_dec (block_enc (x @ xs)) = x @ block_dec (block_enc xs) \<and> block_enc x = enc x"

type_synonym word = "letter list"
type_synonym dbword = "dbit list"
type_synonym bword = "bit list"

(* this function cleans the dirty bword of all dummy characters *)
fun d_clean :: "dbword \<Rightarrow> bword" where
"d_clean [] = []"|
"d_clean (B b # xs) = b # (d_clean xs)"|
"d_clean (D # xs) = d_clean xs"

type_synonym encode = "word \<Rightarrow> dbword"
type_synonym decode = "dbword \<Rightarrow> word"
type_synonym gcode = "encode * decode"
(*
fun binary_encode :: "word => dbword" where
"binary_encode

fun binary_decode :: "dbword \<Rightarrow> word" where

typedef code = "{c :: gcode. \<forall>x y. (fst c) (snd c x) = x \<and> (snd c) (fst c y) = y}"
by
auto
*)
(*
fun lol :: "code \<Rightarrow> int" where
"lol c = 0"

fun qsdf :: "code \<Rightarrow> encode" where
"qsdf c = fst c"
*)
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
(* fixes range *)
assumes distr_i:
"simple_distributed N (Input i) fi"
assumes distr_o:
"simple_distributed N (Output i) fo"
assumes memoryless:
"(m \<noteq> n \<longrightarrow> (indep_var N' (Input m) N' (Output n)) \<and> indep_var N' (Output m) N' (Output n))"
assumes m_info:
"\<I>(Input n ; Output n) > 0"
fixes nn::nat
fixes kk::nat

context information_space_discrete_second
begin
lemma un: "simple_function N (Input i)"
using distr_i simple_distributed_simple_function by blast


(*
fun codelength :: "code \<Rightarrow> prob \<Rightarrow> real" where
\<Sum>l \<in> (`space N)
*)
end
end
