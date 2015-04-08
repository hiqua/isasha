(* This file contains only snippets I found useful to write, just to get to 
know Isabelle a little more, and to enshrine the syntax I sometimes had a hard
time to grasp. *)
theory Snippets
imports Main "~~/src/HOL/Library/Quotient_List"
begin
(*p174 tutorial.pdf: lemmas and rules introduced by typedef *)
typedef 'a alphabet = "{A :: 'a set. (finite A \<and> \<not> ( A = {} ))}" by auto

typedef alph = "{0::nat..<9}"
by (metis atLeastLessThan_iff le0 zero_less_numeral) 

typedef bit = "{0::nat, 1}" apply auto done


class bounded = ord +
fixes max :: "'a"

type_synonym data = "int alphabet"
definition A :: bit where "A \<equiv> Abs_bit 0"
definition B :: data where "B \<equiv> Abs_alphabet {0}"
lemma finnn : "finite (Rep_alphabet B)"
  apply(simp add: B_def)
apply(simp add: Abs_alphabet_inverse)
done


type_synonym ('a,'b) gggcode = "('a list \<Rightarrow> 'b list) "
definition C :: "((int, int) gggcode)" where "C l = []"


typedef finitesymbols = "{s::(nat set). \<exists>n::nat. (1 \<le> n \<and> s = {0::nat..<n})}" by auto
print_theorems

definition exfinite :: finitesymbols where "exfinite \<equiv> Abs_finitesymbols {}"
definition exfinite2 :: finitesymbols where "exfinite2 \<equiv> Abs_finitesymbols {3}"




lemma ds : "n = 0 \<longrightarrow> n \<in> {0::nat..<3}"
apply auto+
done
(*
typedef ggggggcode = "{D :: (letter list\<Rightarrow> letter list) . D [] = [] \<and> (\<forall>x. \<forall> xs. D (x#xs) = (D [x]) @ (D xs))}" 
by auto

type_synonym 'a discret_source = "(nat \<Rightarrow> ('a \<Rightarrow> letter)) set"
*)

definition ex :: bit where "ex \<equiv> Abs_bit (0::nat)"
definition exalph :: "int alphabet" where "exalph == Abs_alphabet {1,2}"

fun folio :: "nat \<Rightarrow> nat" where
  "folio n = n+2"

fun test :: "nat list \<Rightarrow> nat list" where
 "test l = map folio l"

definition intset :: "nat set" where "intset == {0::nat,1}"
lemma azre: "(\<Sum>i\<in>intset. i) = 1"
unfolding intset_def
(* sledgehammer... *)
by simp



locale fake =
fixes zn::nat
begin
(* quotient_type 'a fssset = "'a list" / "(\<lambda>xs ys. set xs = set ys)" *)

fun arbitrary_take :: "'a list \<Rightarrow> 'a list" where
  "arbitrary_take l = take zn l"  

end
end
