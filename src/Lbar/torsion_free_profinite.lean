import for_mathlib.Profinite.extend
import Lbar.basic
import Lbar.functor

universes u v

open_locale nnreal

variables (r' : ℝ≥0) [fact (0 < r')]
variable {S : Profinite.{u}}

set_option pp.universes true

open Lbar Profinite

noncomputable
example : add_comm_group ((extend (Fintype_Lbar.{u u} r')).obj S) :=
begin
  -- haveI : category_theory.small_category.{u+1} Fintype.{u}, sorry,
  -- have := @category_theory.limits.concrete.to_product_injective_of_is_limit
  --   (ProFiltPseuNormGrpWithTinv₁.{u} r') _ _ (Fintype.{u}) _ (Fintype_Lbar.{u u} r'),
  apply_instance,
end

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
