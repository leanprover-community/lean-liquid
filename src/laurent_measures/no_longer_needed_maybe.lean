import data.finset.nat_antidiagonal
import analysis.normed_space.basic
import analysis.specific_limits
import laurent_measures.aux_lemmas

/-  These lemmas seem to no longer be needed for Theorem 6.9 or anywhere else in LTE. -/

open aux_thm69
open metric finset normed_field
open_locale nnreal classical big_operators topological_space

def equiv_Ico_nat_neg {d : ℤ} (hd : d < 0) : {y : {x : ℤ // d ≤ x } // y ∉ T hd} ≃ ℕ :=
begin
  fconstructor,
  { rintro ⟨⟨a, ha⟩, hx⟩,
    exact int.to_nat a },
  { intro n,
    refine ⟨⟨n, hd.le.trans (int.coe_zero_le n)⟩, _⟩,
    apply (not_iff_not_of_iff mem_Ico).mpr,
    simp only [subtype.mk_lt_mk, not_and, not_lt, int.coe_nat_nonneg, implies_true_iff] },
    { rintros ⟨⟨x, dx⟩, hx⟩,
      simp [int.to_nat_of_nonneg (T.zero_le hd hx)] },
    { exact λ n, by simp only [int.to_nat_coe_nat] }
end

lemma equiv_Ico_nat_neg_apply {d : ℤ} (hd : d < 0) {y : {x : ℤ // d ≤ x}} (h : y ∉ T hd) : y.1 = (equiv_Ico_nat_neg hd) ⟨y, h⟩ :=
by { cases y, simp [equiv_Ico_nat_neg, T.zero_le hd h] }

/-  This lemma seems to not be used anywhere. -/
lemma summable_iff_on_nat {f : ℤ → ℝ} {ρ : ℝ≥0} (d : ℤ) (h : ∀ n : ℤ, n < d → f n = 0) :
  summable (λ n, ∥ f n ∥ * ρ ^ n) ↔ summable (λ n : ℕ, ∥ f n ∥ * ρ ^ (n : ℤ)) :=
iff.trans (summable_iff_on_nat_less d (λ n nd, by simp [h _ nd])) iff.rfl

/-  This lemma seems to not be used anywhere. -/
lemma aux_summable_iff_on_nat {f : ℤ → ℝ} {ρ : ℝ≥0} (d : ℤ) (h : ∀ n : ℤ, n < d → f n = 0) :
  summable (λ n, ∥ f n ∥ * ρ ^ n) ↔ summable (λ n : ℕ, ∥ f (n + d) ∥ * ρ ^ (n + d : ℤ)) :=
begin
  have hf : function.support (λ n : ℤ, ∥ f n ∥ * ρ ^ n) ⊆ { a : ℤ | d ≤ a},
  { rw function.support_subset_iff,
    intro x,
    rw [← not_imp_not, not_not, mul_eq_zero],
    intro hx,
    simp only [not_le, set.mem_set_of_eq] at hx,
    apply or.intro_left,
    rw norm_eq_zero,
    exact h x hx },
  have h1 := λ a : ℝ,
    @has_sum_subtype_iff_of_support_subset ℝ ℤ _ _ (λ n : ℤ, ∥ f n ∥ * ρ ^ n) _ _ hf,
  have h2 := λ a : ℝ,
    @equiv.has_sum_iff ℝ {b : ℤ // d ≤ b} ℕ _ _ ((λ n, ∥ f n ∥ * ρ ^ n) ∘ coe) _
    (equiv_bdd_integer_nat d),
  exact exists_congr (λ a, ((h2 a).trans (h1 a)).symm),
end
