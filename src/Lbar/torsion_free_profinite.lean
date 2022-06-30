import algebra.category.Group.limits
import for_mathlib.Profinite.extend
import Lbar.basic
import Lbar.functor
import pseudo_normed_group.category.strictProFiltPseuNormGrpWithTinv

noncomputable theory

universes u v

open_locale nnreal

variables {r' : ℝ≥0} [fact (0 < r')]

set_option pp.universes true

open Lbar Profinite CommGroup category_theory.limits

--[FAE] not needed for LTE, may be for mathlib?
lemma limit_torsion_free_to_Ab
  (C : Type u) [category_theory.small_category C] (J : C ⥤ Ab.{u})
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  : no_zero_smul_divisors ℤ (limit J).α :=
begin
  let L := get_limit_cone _,
  haveI := AddCommGroup.forget_preserves_limits.{u u},
  have h_inj := @concrete.to_product_injective_of_is_limit AddCommGroup.{u} _ _
    C _ J _ L.cone L.is_limit,
  fconstructor,
  intros c x hx,
  let φ := λ x : (limit J), λ j, (L.cone.π.app j) x,
  have h1: φ 0 = 0,
  { ext j,
    exact (L.cone.π.app j).2 },
  have h2: φ (c • x) = c • φ x,
  { ext j,
    exact map_zsmul (L.cone.π.app j) _ _ },
  apply_fun φ at hx,
  simp only [h1, h2, pi.zero_def, function.funext_iff, pi.smul_apply, smul_eq_zero] at hx,
  by_cases hc : c = 0,
  { apply or.intro_left, exact hc},
  { simp only [hc, false_or] at hx,
    apply or.intro_right,
    apply h_inj,
    funext j,
    specialize hx j,
    simp only [_root_.map_zero],
    exact hx },
end

--[FAE] not needed for LTE, may be for mathlib?
lemma add_comm_group.limit_on_nat_torsion_free
  (J : (category_theory.as_small.{u} ℕ) ⥤ AddCommGroup.{u})
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  : no_zero_smul_divisors ℤ (limit J).α := limit_torsion_free_to_Ab (category_theory.as_small.{u} ℕ) J h_tf

lemma limit_torsion_free_to_PFPNGwithTinv {C : Type u} [category_theory.small_category C] (J : C ⥤ (ProFiltPseuNormGrpWithTinv₁.{u} r'))
  [preserves_limit J
    (category_theory.forget.{u+1 u u}(ProFiltPseuNormGrpWithTinv₁.{u} r'))]
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  : no_zero_smul_divisors ℤ (limit J).M :=
begin
  let L := get_limit_cone _,
  have h_inj := @concrete.to_product_injective_of_is_limit (ProFiltPseuNormGrpWithTinv₁.{u} r') _ _ C _ J _ L.cone L.is_limit,
  fconstructor,
  intros c x hx,
  let φ := λ x : limit J, λ j, (L.cone.π.app j) x,
  have h1: φ 0 = 0,
  { ext j,
    exact (L.cone.π.app j).2 },
  have h2: φ (c • x) = c • φ x,
  { ext j,
    apply comphaus_filtered_pseudo_normed_group_with_Tinv_hom.map_zsmul },
  apply_fun φ at hx,
  simp only [h1, h2, pi.zero_def, function.funext_iff, pi.smul_apply, smul_eq_zero] at hx,
  by_cases hc : c = 0,
  { apply or.intro_left, exact hc},
  { simp only [hc, false_or] at hx,
    apply or.intro_right,
    apply h_inj,
    funext j,
    specialize hx j,
    simp only [comphaus_filtered_pseudo_normed_group_with_Tinv_hom.map_zero],
    exact hx },
end

instance (S : Profinite.{u}) : preserves_limit (fintype_diagram S ⋙ Fintype_Lbar.{u u} r') (category_theory.forget.{u+1 u u}(ProFiltPseuNormGrpWithTinv₁.{u} r')) := sorry

instance (S : Profinite.{u}) : no_zero_smul_divisors ℤ ((extend (Fintype_Lbar.{u u} r')).obj S) :=
begin
  apply limit_torsion_free_to_PFPNGwithTinv (fintype_diagram S ⋙ Fintype_Lbar.{u u} r'),
  intro _,
  exact Fintype.Lbar_no_zero_smul_divisors.{u} _ r',
end
