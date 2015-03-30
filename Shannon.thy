theory Shannon
imports Information
begin
typedef bit = "{0::nat,1}" apply auto done
typedef 'a alphabet = "{A :: 'a set.(finite A \<and> \<not> ( A = {} ))}" apply auto done
type_synonym data = int --"int alphabet"

(* 
X is the input, Y is the output.
They are not independent (if they are, all of this serves no purpose)
We fix N, N' the measures (TODO: should I? Can we have two different bit measures?)
The input is only correlated to the corresponding output.
*)

locale information_space_discrete = information_space +
  fixes Input :: "nat \<Rightarrow> ('a \<Rightarrow> data)"
  fixes Output :: "nat \<Rightarrow> ('a \<Rightarrow> data)"
  fixes fi :: "data \<Rightarrow> real"
  fixes fo :: "data \<Rightarrow> real"
  fixes N :: "'a measure"
  fixes N' :: "data measure"
  assumes distr_i:
    "simple_distributed N (Input i) fi"
  assumes distr_o:
    "simple_distributed N (Output i) fo"
  assumes memoryless:
 "(m \<noteq> n \<longrightarrow> (indep_var N' (Input m) N' (Output n)) \<and> indep_var N' (Output m) N' (Output n))"
 assumes io_corr:
 "\<not> indep_var N' (Input n) N' (Output n)"

context information_space_discrete
begin

(* fake lemma, just to get used to structured proofs *)
(*
lemma test: "prob_space.expectation N (Input i) = prob_space.expectation N (Input j)"
proof -
have 0: "i = j \<longrightarrow> prob_space.expectation N (Input i) = prob_space.expectation N (Input j)"
by auto
have 1: "i \<noteq> j \<longrightarrow>prob_space.expectation N (Input i) = prob_space.expectation N (Input j)"
  proof
    have 2: "density N (Input i) = density N (Input j)" using simple_distributed
sorry
*)


end
end
