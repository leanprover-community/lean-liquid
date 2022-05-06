import algebra.category.Group.abelian
import algebra.category.Group.limits

import for_mathlib.is_iso_neg
import for_mathlib.homology_iso
import for_mathlib.SemiNormedGroup

import system_of_complexes.basic
.

noncomputable theory

open_locale nnreal

open category_theory category_theory.limits opposite

namespace system_of_complexes

-- show that `Ab.{u}` has limits indexed by `ℕ`.
instance (f : ℕ → Ab) : has_product f := sorry

variables (C : system_of_complexes) (i : ℕ) (f : ℕ → ℝ≥0)

def shift (hf : monotone f) :
  (∏ (λ x : ℕ, (C.to_Ab.obj (op $ f x)).homology i)) ⟶
  (∏ (λ x : ℕ, (C.to_Ab.obj (op $ f x)).homology i)) :=
pi.lift $ λ x, pi.π _ (x+1) ≫ (homology_functor _ _ i).map
  (C.to_Ab.map (hom_of_le $ hf $ nat.le_succ x).op)

def shift_sub_id (hf : monotone f) :
  (∏ (λ x : ℕ, (C.to_Ab.obj (op $ f x)).homology i)) ⟶
  (∏ (λ x : ℕ, (C.to_Ab.obj (op $ f x)).homology i)) :=
C.shift i f hf - 𝟙 _

variables [∀ c i, complete_space (C c i)] [∀ c i, separated_space (C c i)]

lemma _root_.category_theory.homology.π_eq_zero
  {A B C : Ab} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) (x)
  (h : ∃ a : A, f a = (kernel_subobject g).arrow x) :
  homology.π f g w x = 0 :=
begin
  rcases h with ⟨a, ha⟩,
  sorry
end

lemma shift_eq_zero (hf : monotone f) {k K c₀ : ℝ≥0} [fact (1 ≤ k)]
  (hC : C.is_bounded_exact k K i c₀)
  (hc₀ : ∀ j, c₀ ≤ f j) (hk : ∀ j, k * f j ≤ f (j+1)) :
  C.shift i f hf = 0 :=
begin
  apply category_theory.limits.limit.hom_ext, intros j,
  rw [zero_comp, shift, limit.lift_π, fan.mk_π_app, homology_functor_map],
  convert comp_zero using 2,
  apply homology.ext,
  rw [comp_zero, homology.π_map],
  apply AddCommGroup.ext, intros x,
  let d := homological_complex.d_from (C.to_Ab.obj (op (f (j + 1)))) i,
  let x' : C (f (j+1)) i := (kernel_subobject d).arrow x,
  have aux : fact (c₀ ≤ f j) := ⟨hc₀ _⟩,
  haveI : fact (k * f j ≤ f (j+1)) := ⟨hk _⟩,
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC (f j) aux i le_rfl (res x'),
  have hdx' : C.d i (i+1) x' = 0,
  { show ((kernel_subobject d).arrow ≫ ((C.to_Ab.obj (op (f (j+1)))).d i (i+1))) x = 0,
    suffices : (kernel_subobject d).arrow ≫ (C.to_Ab.obj (op (f (j+1)))).d i (i+1) = 0,
    { rw this, refl },
    rw [← (C.to_Ab.obj (op (f (j+1)))).d_from_comp_X_next_iso, ← category.assoc,
      kernel_subobject_arrow_comp, zero_comp],
    dsimp, refl, },
  rw [res_res, d_res, hdx', normed_group_hom.map_zero, norm_zero, mul_zero,
    ← coe_nnnorm, ← nnreal.coe_zero, nnreal.coe_le_coe, le_zero_iff,
    nnnorm_eq_zero, sub_eq_zero] at hy,
  apply category_theory.homology.π_eq_zero,
  cases i,
  { refine ⟨0, _⟩,
    simp only [homological_complex.d_to_eq_zero, cochain_complex.prev_nat_zero,
      AddCommGroup.zero_apply, kernel_subobject_map_arrow_apply,
      homological_complex.hom.sq_from_left],
    rw d_eq_zero at hy, { exact hy.symm }, { dec_trivial } },
  { refine ⟨((C.to_Ab.obj (op (f j))).X_prev_iso _).inv y, _⟩,
    { dsimp, refl },
    rw [← comp_apply, ← comp_apply, homological_complex.X_prev_iso_comp_d_to,
      kernel_subobject_map_arrow],
    exact hy.symm, },
end

lemma shift_sub_id_is_iso (hf : monotone f) {k K c₀ : ℝ≥0} [fact (1 ≤ k)]
  (hC : C.is_bounded_exact k K i c₀)
  (hc₀ : ∀ j, c₀ ≤ f j) (hk : ∀ j, k * f j ≤ f (j+1)) :
  is_iso (C.shift_sub_id i f hf) :=
begin
  rw [shift_sub_id, shift_eq_zero C i f hf hC hc₀ hk, zero_sub, is_iso_neg_iff],
  apply_instance
end

end system_of_complexes
