import algebra.category.Group.abelian
import algebra.category.Group.limits

import for_mathlib.is_iso_neg
import for_mathlib.homology_iso
import for_mathlib.SemiNormedGroup
import for_mathlib.AddCommGroup.pt

import system_of_complexes.basic
.

noncomputable theory

universe u

open_locale nnreal

open category_theory category_theory.limits opposite

set_option pp.universes true

lemma category_theory.homology.π_eq_zero
  {A B C : Ab.{u}} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) (x)
  (h : ∃ a : A, f a = (kernel_subobject g).arrow x) :
  homology.π f g w x = 0 :=
begin
  rcases h with ⟨a, ha⟩,
  rw [Ab.apply_eq_pt_comp _ a, Ab.apply_eq_pt_comp _ x,
    ← image_subobject_arrow_comp f, ← image_to_kernel_arrow _ _ w,
    ← category.assoc, ← category.assoc] at ha,
  have : (Ab.pt a ≫ factor_thru_image_subobject f) ≫ image_to_kernel f g w = Ab.pt x,
  { rw ← cancel_mono (kernel_subobject g).arrow,
    let e : ℤ ≃+ ulift.{u} ℤ := add_equiv.ulift.symm,
    have he : function.surjective e.to_add_monoid_hom := e.surjective,
    refine (add_monoid_hom.cancel_right he).mp _,
    ext, exact ha, },
  rw [Ab.apply_eq_pt_comp, ← this, category.assoc, homology.condition, comp_zero],
  refl,
end

-- move me, generalize
instance ulift.preorder : preorder (ulift.{u} ℕ) :=
preorder.lift ulift.down

section

variables (C : ℝ≥0ᵒᵖ ⥤ Ab.{u}) (i : ℕ) (f : ulift.{u} ℕ → ℝ≥0)

def shift_sub_id.shift (hf : monotone f) :
  (∏ (λ x, C.obj (op $ f x))) ⟶ (∏ (λ x, C.obj (op $ f x))) :=
pi.lift $ λ x, pi.π _ (⟨x.down+1⟩) ≫ (C.map (hom_of_le $ hf $ by apply nat.le_succ).op)

def shift_sub_id (hf : monotone f) :
  (∏ (λ x, C.obj (op $ f x))) ⟶ (∏ (λ x, C.obj (op $ f x))) :=
shift_sub_id.shift C f hf - 𝟙 _

end

namespace system_of_complexes

variables (C : system_of_complexes.{u}) (i : ℕ) (f : ulift.{u} ℕ → ℝ≥0)

def to_AbH : ℝ≥0ᵒᵖ ⥤ Ab := C.to_Ab ⋙ homology_functor _ _ i

variables [∀ c i, complete_space (C c i)] [∀ c i, separated_space (C c i)]

lemma shift_eq_zero (hf : monotone f) {k K c₀ : ℝ≥0} [fact (1 ≤ k)]
  (hC : C.is_bounded_exact k K i c₀)
  (hc₀ : ∀ j, c₀ ≤ f j) (hk : ∀ j, k * f j ≤ f (j+1)) :
  shift_sub_id.shift (C.to_AbH i) f hf = 0 :=
begin
  apply category_theory.limits.limit.hom_ext, intros j,
  rw [zero_comp, shift_sub_id.shift, to_AbH, limit.lift_π, fan.mk_π_app,
    functor.comp_map, homology_functor_map],
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
  is_iso (shift_sub_id (C.to_AbH i) f hf) :=
begin
  rw [shift_sub_id, shift_eq_zero C i f hf hC hc₀ hk, zero_sub, is_iso_neg_iff],
  apply_instance
end

end system_of_complexes
