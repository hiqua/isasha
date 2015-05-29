(* This file contains only snippets I found useful to write, just to get to
know Isabelle a little more, and to enshrine the syntax I sometimes had a hard
time to grasp. *)
theory Snippets
imports Main "~~/src/HOL/Library/Quotient_List" Real
begin
(*p174 tutorial.pdf: lemmas and rules introduced by typedef *)
typedef 'a alphabet = "{A :: 'a set. (finite A \<and> \<not> ( A = {} ))}" by auto

typedef alph = "{0::nat..<9}"
by (metis atLeastLessThan_iff le0 zero_less_numeral)

typedef bit = "{0::nat, 1}" apply auto done

lemma "\<exists>c. x \<le> 0 \<Longrightarrow> ln x = c"
proof -
fix c::real
assume "c = (THE x. False)"
then have "x\<le>0 \<Longrightarrow> ln x = c"
 using ln_neg_is_const by simp

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


locale dummy =
fixes a::nat
fixes b::'b
fixes bc::"'b list"
assumes "a = length bc"
print_locale dummy

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
assumes "\<forall>x. (length x) \<le> len_of TYPE ('a) \<Longrightarrow>  dec (enc x) = x"

class block_coded = coded +
fixes block_enc :: "'a list \<Rightarrow> bit list"
fixes block_dec :: "bit list \<Rightarrow> 'a list"
assumes block_corresp1:
"\<forall>x.\<forall>xs. (length x) = len_of TYPE('a) \<Longrightarrow>
block_dec (block_enc (x @ xs)) = x @ block_dec (block_enc xs)"
assumes block_corresp2:
"\<forall>x. (length x) \<le> len_of TYPE('a) \<Longrightarrow>
block_enc x = enc x \<and> block_dev enc x = x"

type_synonym bword = "bit list"
datatype dbit = B bit | D
type_synonym dbword = "dbit list"
(* this function cleans the dirty bword of all dummy characters *)
fun d_clean :: "dbword \<Rightarrow> bword" where
"d_clean [] = []"|
"d_clean (B b # xs) = b # (d_clean xs)"|
"d_clean (D # xs) = d_clean xs"



locale fake =
fixes zn::nat
begin
(* quotient_type 'a fssset = "'a list" / "(\<lambda>xs ys. set xs = set ys)" *)

fun arbitrary_take :: "'a list \<Rightarrow> 'a list" where
  "arbitrary_take l = take zn l"


lemma sum_transform_aux:
assumes bounded: "\<forall>x \<in> H. f x < (Suc m::nat)"
shows "finite H \<Longrightarrow> (\<Sum>x\<in>H\<inter>f-`{i}.f x) = i * card (f-`{i} \<inter> H)"
proof auto
assume "finite H"
hence "card (H \<inter> (f -` {i})) = card ((f -` {i}) \<inter> H)"
using Set.Int_commute[where A=H]
by simp
thus "finite H \<Longrightarrow> card (H \<inter> f -` {i}) \<noteq> card (f -` {i} \<inter> H) \<Longrightarrow> i = 0"
by auto
qed


lemma partition:
assumes bounded: "\<forall>x \<in> H. f x < (Suc m::nat)"
shows "finite H \<Longrightarrow> H = (\<Union>i \<in> {0..m}. ( H\<inter>f-`{i}))" using bounded by auto


lemma sum_vimage_proof_aux2:
" ((n::nat) + 1) * g = (n* g + g)"
apply auto
done


lemma sum_vimage_proof_aux22:
"real ((n::int) + 1) * g = (n* g + g)"
apply auto+
apply algebra
done

lemma sum_vimage_proof_aux222:
"real ((n::nat) + 1) * g = (n* g + g)"
apply auto
apply (metis comm_monoid_mult_class.mult.right_neutral distrib_left mult.commute real_of_nat_Suc)
done



lemma sum_rw:
fixes b::real
fixes f::"nat \<Rightarrow> real"
assumes "finite F" "E \<subseteq> F"
shows "(\<Sum>i| i \<in>F. f i * log b (f i))
= (\<Sum>i|i \<in> (F-E). f i * log b (f i))
+(\<Sum>i|i \<in> E. f i * log b (f i))" using Groups_Big.setsum_diff[OF assms, of f]
by (metis (no_types) Collect_mem_eq assms(1) assms(2) setsum.subset_diff)


type_synonym ty = "nat list"
locale loc =
fixes i::'b
fixes fi :: "'b \<Rightarrow> real"
assumes 3: "fi i = 3"
begin
lemma lem: "\<And>j. fi j \<noteq> 3 \<Longrightarrow> j \<noteq> i" using 3 by auto

end

definition len :: "'c list \<Rightarrow> real" where
  "len t = length t"

interpretation ty: loc "[3::nat,1,3]" "len"
proof unfold_locales
show "len [3::nat,1,3] = 3" unfolding len_def by simp
qed

lemma qsdf: "\<And>j. len j \<noteq> 3 \<Longrightarrow> j \<noteq> [3::nat,1,3]" using ty.lem by simp


end
end
