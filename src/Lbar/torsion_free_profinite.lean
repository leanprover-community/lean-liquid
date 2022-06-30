import algebra.category.Group.limits
import for_mathlib.Profinite.extend
import Lbar.basic
import Lbar.functor

universes u v

open_locale nnreal

variables (r' : ℝ≥0) [fact (0 < r')]
variable {S : Profinite.{u}}

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

lemma add_comm_group.limit_torsion_free
  (J : (category_theory.as_small.{u} ℕ) ⥤ AddCommGroup.{u})
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  : no_zero_smul_divisors ℤ (category_theory.limits.limit J).α :=
begin
  let L : limit_cone.{u u u u+1} J := get_limit_cone _,
  haveI : preserves_limit.{u u u u u+1 u+1} J (category_theory.forget.{u+1 u u} AddCommGroup.{u}),
  apply preserves_limit_of_preserves_limit_cone.{u u u u u+1 u+1} L.2 _,
  sorry,
  have h_inj := @concrete.to_product_injective_of_is_limit AddCommGroup.{u} _ _
    (category_theory.as_small.{u} ℕ) _ J _ L.cone L.is_limit,
  fconstructor,
  intros c x hx,
  let φ := λ x : (limit.{u u u u+1} J).α, λ j, (L.cone.π.app j) x,
  have h1: φ 0 = 0, sorry,
  have h2: φ (c • x) = c • φ x, sorry,
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

-- lemma limit_torsion_free (J : ℕ ⥤ (ProFiltPseuNormGrpWithTinv₁.{u} r'))
--   (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
--   (h_lim : category_theory.limits.has_limit J) :
--     no_zero_smul_divisors ℤ (category_theory.limits.limit J).M :=
-- begin
--   refine add_comm_group.limit_torsion_free J h_tf h_lim,
-- end

lemma torsion_free_profinite (n : ℤ) (x : (extend (Fintype_Lbar.{u u} r')).obj S) :
  n • x = 0 → n = 0 ∨ x = 0:=
begin
  intro hx,
  dsimp at x,--[FAE] look at `Lbar.basic.lean`, l. 445 the map `map` for the def'n of transitionss
  sorry,
end

instance : no_zero_smul_divisors ℤ ((extend (Fintype_Lbar.{u u} r')).obj S) :=
begin
  fconstructor,
  intros c x hx,
  apply torsion_free_profinite r' c x hx,
end
