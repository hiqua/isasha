theory Shannon
imports Information
begin
typedef bit = "{0::nat,1}" apply auto done

(* 
X is the input, Y is the output.
They are not independent (if they are, all of this serves no purpose)
We fix N the bit measure (TODO: should we?)
The input is only correlated to the corresponding output.
*)

locale information_space_discrete = information_space +
  fixes Input :: "nat \<Rightarrow> ('a \<Rightarrow> bit)"
  fixes Output :: "nat \<Rightarrow> ('a \<Rightarrow> bit)"
  fixes X :: "'a \<Rightarrow> bit"
  fixes Y :: "'a \<Rightarrow> bit"
  fixes N :: "bit measure"
  assumes "random_variable N (Input n)"
  assumes "random_variable N (Output n)"
  assumes "m \<noteq> n \<longleftrightarrow> (indep_var N (Input m) N (Output n))"
end
