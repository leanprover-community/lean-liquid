import algebra.category.Group.abelian
import algebra.category.Group.limits

import for_mathlib.is_iso_neg
import for_mathlib.homology_iso

import system_of_complexes.basic
.

noncomputable theory

open_locale nnreal

open category_theory category_theory.limits opposite

namespace system_of_complexes

variables (C : system_of_complexes)

-- show that `Ab.{u}` has limits indexed by `ℕ`.
instance (f : ℕ → Ab) : has_product f := sorry

def shift (C : system_of_complexes) (i : ℕ) (f : ℕ → ℝ≥0) (hf : monotone f) :
  (∏ (λ x : ℕ, (C.to_Ab.obj (op $ f x)).homology i)) ⟶
  (∏ (λ x : ℕ, (C.to_Ab.obj (op $ f x)).homology i)) :=
pi.lift $ λ x, pi.π _ (x+1) ≫ (homology_functor _ _ i).map
  (C.to_Ab.map (hom_of_le $ hf $ nat.le_succ x).op)

def shift_sub_id (C : system_of_complexes) (i : ℕ) (f : ℕ → ℝ≥0) (hf : monotone f) :
  (∏ (λ x : ℕ, (C.to_Ab.obj (op $ f x)).homology i)) ⟶
  (∏ (λ x : ℕ, (C.to_Ab.obj (op $ f x)).homology i)) :=
C.shift i f hf - 𝟙 _

lemma shift_eq_zero (C : system_of_complexes) (i : ℕ) (f : ℕ → ℝ≥0) (hf : monotone f)
  {k K c₀ : ℝ≥0} [fact (1 ≤ k)]
  (hC : C.is_bounded_exact k K (i+1) c₀) :
  C.shift i f hf = 0 :=
begin
  apply category_theory.limits.limit.hom_ext, intros j,
  rw [zero_comp, shift, limit.lift_π, fan.mk_π_app, homology_functor_map],
  convert comp_zero using 2,
  apply homology.ext,
  rw [comp_zero, homology.π_map],
  apply AddCommGroup.ext, intros x,
  have := hC (f j + 1),
  sorry
end

lemma shift_sub_id_is_iso (C : system_of_complexes) (i : ℕ) (f : ℕ → ℝ≥0) (hf : monotone f)
  {k K c₀ : ℝ≥0} [fact (1 ≤ k)]
  (hC : C.is_bounded_exact k K (i+1) c₀) :
  is_iso (C.shift_sub_id i f hf) :=
begin
  rw [shift_sub_id, shift_eq_zero C i f hf hC, zero_sub, is_iso_neg_iff],
  apply_instance
end

end system_of_complexes
