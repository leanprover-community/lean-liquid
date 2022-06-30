import algebra.category.Group.limits
import for_mathlib.Profinite.extend
import Lbar.basic
import Lbar.functor
import pseudo_normed_group.category.strictProFiltPseuNormGrpWithTinv

universes u v

open_locale nnreal

variables (r' : ℝ≥0) [fact (0 < r')]

set_option pp.universes true

open Lbar Profinite CommGroup category_theory.limits

noncomputable
example (r' : ℝ≥0) [fact (0 < r')] {S : Profinite.{u}} : AddCommGroup.{u} :=
begin
  let uno := ((extend (Fintype_Lbar.{u u} r')).obj S),
  use uno,
  -- let due := S.fintype_diagram ⋙ Fintype_Lbar.{u u} r',
  -- haveI : category_theory.small_category.{u+1} Fintype.{u}, sorry,
  -- have := @category_theory.limits.concrete.to_product_injective_of_is_limit
  --   (ProFiltPseuNormGrpWithTinv₁.{u} r') _ _ (Fintype.{u}) _ (Fintype_Lbar.{u u} r'),
  apply_instance,
end

lemma add_comm_group.limit_on_nat_torsion_free
  (J : (category_theory.as_small.{u} ℕ) ⥤ AddCommGroup.{u})
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  : no_zero_smul_divisors ℤ (limit J).α :=
begin
  let L := get_limit_cone _,
  haveI := AddCommGroup.forget_preserves_limits.{u u},
  have h_inj := @concrete.to_product_injective_of_is_limit AddCommGroup.{u} _ _
    (category_theory.as_small.{u} ℕ) _ J _ L.cone L.is_limit,
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

lemma profinitely_filtered_pseudo_normed_group_with_Tinv.limit_on_nat_torsion_free (J : (category_theory.as_small.{u} ℕ) ⥤ (ProFiltPseuNormGrpWithTinv₁.{u} r'))
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  : no_zero_smul_divisors ℤ (limit J).M :=
begin
  let L := get_limit_cone _,
  haveI : preserves_limit J
    (category_theory.forget.{u+1 u u}(ProFiltPseuNormGrpWithTinv₁.{u} r')), sorry,
  have h_inj := @concrete.to_product_injective_of_is_limit (ProFiltPseuNormGrpWithTinv₁.{u} r') _ _
    (category_theory.as_small.{u} ℕ) _ J _ L.cone L.is_limit,
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

instance : category_theory.small_category.{u+1} Fintype.{u} := sorry

lemma profinitely_filtered_pseudo_normed_group_with_Tinv.limit_on_Fin_torsion_free
  (J : @category_theory.functor.{u u} Fintype.{u} _(ProFiltPseuNormGrpWithTinv₁.{u} r') _)
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  [category_theory.limits.has_limit J] :
    no_zero_smul_divisors ℤ (limit J).M :=
begin
  let L := get_limit_cone J,
  haveI : preserves_limit J (category_theory.forget (ProFiltPseuNormGrpWithTinv₁.{u} r')),
    sorry,
  have h_inj : function.injective (λ x : L.cone.X, λ j, L.cone.π.app j x),
  have := @concrete.to_product_injective_of_is_limit,
  sorry,
  -- have h_inj := @concrete.to_product_injective_of_is_limit (ProFiltPseuNormGrpWithTinv₁.{u} r') _ _
  --   Fintype.{u} _ J _ L.cone L.is_limit,
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

-- noncomputable
-- lemma Fintype.torsion_free_Lbar (S : Fintype.{u}) (n : ℤ)  :
--   no_zero_smul_divisors ℤ ((Fintype_Lbar.{u u} r').obj S) :=
--   -- (x : (Fintype_Lbar.{u u} r').obj S) : n • x = 0 → n = 0 ∨ x = 0 :=
-- begin
--   -- intro hx,
--   -- dsimp at x,--[FAE] look at `Lbar.basic.lean`, l. 445 the map `map` for the def'n of transitionss
--   have := profinitely_filtered_pseudo_normed_group_with_Tinv.limit_on_Fin_torsion_free.{u} r' ((Fintype_Lbar.{u u} r')),
--   apply this,
-- end

lemma Profinite.torsion_free_Lbar (S : Profinite.{u}) (n : ℤ) (x : (extend (Fintype_Lbar.{u u} r')).obj S) : n • x = 0 → n = 0 ∨ x = 0 :=
begin
  intro hx,
  dsimp at x,--[FAE] look at `Lbar.basic.lean`, l. 445 the map `map` for the def'n of transitionss
  have := profinitely_filtered_pseudo_normed_group_with_Tinv.limit_on_Fin_torsion_free.{u} r' ((Fintype_Lbar.{u u} r')),
  sorry,
end

variable (S : Profinite.{u})

instance : no_zero_smul_divisors ℤ ((extend (Fintype_Lbar.{u u} r')).obj S) :=
begin
  fconstructor,
  intros c x hx,
  exact S.torsion_free_Lbar r' c x hx,
end
