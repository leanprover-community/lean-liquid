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

-- noncomputable
lemma add_comm_group.limit_torsion_free
  (J : (category_theory.as_small.{u} ℕ) ⥤ AddCommGroup.{u})
  -- (J : (ulift.{u} ℕ) ⥤ (ulift.{u} ℕ)) : true :=
  (h_tf : ∀ j, no_zero_smul_divisors ℤ (J.obj j))
  (h_lim : category_theory.limits.has_limit J)
  : no_zero_smul_divisors ℤ (category_theory.limits.limit J).α :=
begin
  have L : limit_cone.{u u u u+1} J, sorry,
  -- haveI : category_theory.concrete_category.{u} ℕ, sorry,?
  -- have := @preserves_limit (category_theory.as_small ℕ) _ (category_theory.as_small ℕ) _,
  -- haveI : category_theory.small_category.{u} (ulift.{u} ℕ), sorry,
  haveI : preserves_limit.{u u u u u+1 u+1} J (category_theory.forget.{u+1 u u} AddCommGroup.{u}), sorry,
  -- have := concrete.to_product_injective_of_is_limit J,
  have := @concrete.to_product_injective_of_is_limit AddCommGroup.{u} _ _
    (category_theory.as_small.{u} ℕ) _ J _ L.cone L.is_limit,
    sorry,
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
