import Lbar.ses
import Lbar.finsupp_instance

universe u

noncomputable theory
open_locale big_operators nnreal
open pseudo_normed_group category_theory category_theory.limits aux_thm69 laurent_measures

local attribute [instance] type_pow

variables {r' : ℝ≥0} [fact (0 < r')] [fact (r' < 1)] {S : Fintype}
  (F : laurent_measures r' S) (s : S)

/--  Given `F : laurent_measures r' S`, for each `s : S`, `tail F s` is the restriction of `F s` to
the non-positive indices, with opposite sign, i.e. a finsupp `ℕ →₀ ℤ`.
Taken together `tail F` is a term of type `invpoly r' ⟨S⟩`. -/
def tail : invpoly r' ⟨S⟩ :=
λ s, ⟨begin
    refine set.finite.to_finset (_ : {n : ℕ | ∃ m : ℤ, m = -n ∧ F s (m) ≠ 0}.finite),
    obtain ⟨d, h⟩ := exists_bdd_filtration (fact.out _ : 0 < r') (fact.out _ : r' < 1) F,
    refine ((finset.range (-d + 1).to_nat).finite_to_set).subset (λ n hn, _),
    rw [set.mem_set_of_eq, exists_eq_left] at hn,
    rw [finset.mem_coe, finset.mem_range, int.lt_to_nat],
    exact not_le.mp (λ nd, hn $ h s (- n) $ neg_lt.mp $ int.add_one_le_iff.mp nd)
  end,
 λ n, F s (-(n : ℤ)),
 by simp only [set.mem_set_of_eq, exists_eq_left, set.finite.mem_to_finset, iff_self, forall_const]⟩

lemma tail_of_nonneg {n : ℕ} : (tail F s n) = F s (- n) :=
by simp only [tail, finsupp.coe_mk]

lemma int.tail_of_nonneg {n : ℤ} (n0 : 0 ≤ n) : tail F s n.to_nat = F s (- n) :=
(tail_of_nonneg F s).trans $ congr_arg _ $ congr_arg _ $ int.to_nat_of_nonneg n0

lemma ite_to_Lbar_tail (n : ℤ) :
  ite (0 < n) ((to_Lbar r' S F).to_fun s n.to_nat) (tail F s (-n).to_nat) = F s n :=
begin
  by_cases n0 : 0 < n,
  { have : n.to_nat ≠ 0,
    { simpa using (lt_of_lt_of_le n0 (int.to_nat_of_nonneg n0.le).ge).ne' },
    simp only [n0, to_Lbar, if_true, this, int.to_nat_of_nonneg n0.le, if_false] },
  { rw [if_neg n0, int.tail_of_nonneg F s (neg_nonneg.mpr (not_lt.mp n0)), neg_neg] }
end
