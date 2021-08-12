import data.fintype.intervals
import analysis.specific_limits
import category_theory.Fintype
import analysis.normed_space.basic

import pseudo_normed_group.basic
import pseudo_normed_group.category

universe u

noncomputable theory
open_locale big_operators nnreal
open set

instance (k₁ k₂ : ℤ) : fintype (Icc k₁ k₂) := (Icc_ℤ_finite _ _).some

structure laurent_measures_bdd (r : ℝ≥0) (S : Fintype) (T : finset ℤ) (c : ℝ≥0) :=
(to_fun : S → T → ℤ)
(bound' : ∑ s i, ∥ to_fun s i ∥ * (r : ℝ) ^ (i : ℤ) ≤ c)

namespace laurent_measures_bdd

variables {r : ℝ≥0} {S : Fintype} {T : finset ℤ} {c : ℝ≥0}

instance : has_coe_to_fun (laurent_measures_bdd r S T c) :=
⟨λ _, S → T → ℤ, λ F, F.1⟩

instance : has_norm (laurent_measures_bdd r S T c) :=
⟨λ F, ∑ s i, ∥ F s i ∥ * (r : ℝ)^(i : ℤ)⟩

@[ext]
lemma ext (F G : laurent_measures_bdd r S T c) :
  (F : S → T → ℤ) = G  → F = G := by {intros h, cases F, cases G, simpa }

@[simp]
lemma norm_def (F : laurent_measures_bdd r S T c) : ∥ F ∥ =
  ∑ s i, ∥ F s i ∥ * (r : ℝ)^(i : ℤ) := rfl

lemma bound (F : laurent_measures_bdd r S T c) :
  ∥ F ∥ ≤ c := F.2

lemma coeff_bound (F : laurent_measures_bdd r S T c) [hr : fact (0 < r)]
  (s : S) (i : T) : ∥ F s i ∥ ≤ c * ((r : ℝ)^(i : ℤ))⁻¹ :=
begin
  suffices : ∥ F s i ∥ * (r : ℝ)^(i : ℤ) ≤ c,
  { have hh : 0 < ((r : ℝ)^(i : ℤ))⁻¹,
    { rw [inv_pos],
      refine fpow_pos_of_pos _ _,
      exact_mod_cast hr.out },
    have hh' : (r : ℝ)^(i : ℤ) ≠ 0,
    { apply fpow_ne_zero,
      apply ne_of_gt,
      exact_mod_cast hr.out },
    convert mul_le_mul this (le_refl _) (le_of_lt hh) _,
    { field_simp [this] },
    exact nnreal.coe_nonneg c },
  refine le_trans _ F.bound,
  have : ∑ i, ∥ F s i ∥ * (r : ℝ)^(i : ℤ) ≤ ∥ F ∥,
  { apply @finset.single_le_sum S ℝ _ (λ s, ∑ i, ∥ F s i ∥ * (r : ℝ)^(i : ℤ)),
    { rintros s -,
      apply finset.sum_nonneg,
      rintros i -,
      refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
      exact nnreal.coe_nonneg r },
    { simp } },
  refine le_trans _ this,
  apply @finset.single_le_sum T ℝ _ (λ i, ∥ F s i∥ * (r : ℝ)^(i : ℤ)),
  { rintros i -,
    refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
    exact nnreal.coe_nonneg r },
  { simp }
end

open_locale classical

instance (r : ℝ≥0) [fact (0 < r)] (S : Fintype) (T : finset ℤ) :
  fintype (laurent_measures_bdd r S T c) :=
begin
  let lb : T → ℤ := λ i, floor (-((c : ℝ) * ((r : ℝ)^(i : ℤ))⁻¹)),
  let ub : T → ℤ := λ i, ceil ((c : ℝ) * ((r : ℝ)^(i : ℤ))⁻¹),
  let ι : laurent_measures_bdd r S T c →
    (Π (s : S) (i : T), Icc (lb i) (ub i)) :=
    λ F s i, ⟨F s i, _⟩,
  apply fintype.of_injective ι _,
  { intros F G h,
    ext s i,
    apply_fun (λ e, (e s i : ℤ)) at h,
    exact h },
  { have := F.coeff_bound s i,
    change (abs (F s i) : ℝ) ≤ _ at this,
    rw abs_le at this,
    split,
    { exact_mod_cast le_trans (floor_le _) this.1 },
    { exact_mod_cast le_trans this.2 (le_ceil _) } }
end

instance : topological_space (laurent_measures_bdd r S T c) := ⊥

example [fact (0 < r)] : compact_space (laurent_measures_bdd r S T c) :=
  by apply_instance

example : t2_space (laurent_measures_bdd r S T c) := by apply_instance

example : totally_disconnected_space (laurent_measures_bdd r S T c) :=
  by apply_instance

end laurent_measures_bdd
