import condensed.ab
import condensed.short_exact

import for_mathlib.AddCommGroup.explicit_products

open_locale classical big_operators

open category_theory
open category_theory.limits
open opposite

namespace Condensed

universes u
variables (F : as_small.{u+1} ℕ ⥤ Condensed.{u} Ab.{u+1})

noncomputable theory

def coproduct_to_colimit : (∐ F.obj) ⟶ colimit F :=
sigma.desc (λ i, colimit.ι _ i)

def coproduct_to_coproduct :
  (∐ F.obj) ⟶ (∐ F.obj)  :=
sigma.desc $ λ i,
  F.map (as_small.up.map $ hom_of_le $ nat.le_succ _) ≫
  sigma.ι _ (as_small.up.obj (as_small.down.obj i + 1))

instance epi_coproduct_to_colimit :
  epi (coproduct_to_colimit F) :=
begin
  constructor,
  intros Z a b h,
  apply colimit.hom_ext,
  intros j,
  apply_fun (λ e, sigma.ι F.obj j ≫ e) at h,
  dsimp [coproduct_to_colimit] at h,
  simpa using h,
end

def sigma_eval_iso {α : Type (u+1)} (X : α → Condensed.{u} Ab.{u+1})
  (S : ExtrDisc.{u}) :
  (∐ X).val.obj (op S.val) ≅ ∐ (λ a, (X a).val.obj (op S.val)) :=
preserves_colimit_iso (Condensed.evaluation _ S.val) _ ≪≫
has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ i, iso.refl _)

@[reassoc]
lemma ι_sigma_eval_iso {α : Type (u+1)} (X : α → Condensed.{u} Ab.{u+1})
  (S : ExtrDisc.{u}) (i : α) :
  (sigma.ι X i : X i ⟶ _).val.app (op S.val) ≫
  (sigma_eval_iso X S).hom = sigma.ι _ i :=
begin
  dsimp only [sigma_eval_iso],
  erw (is_colimit_of_preserves (Condensed.evaluation _ S.val) _).fac_assoc,
  erw colimit.ι_desc, dsimp, simp,
end

def sigma_eval_iso_direct_sum
  {α : Type (u+1)} (X : α → Condensed.{u} Ab.{u+1})
  (S : ExtrDisc.{u}) :
  (∐ X).val.obj (op S.val) ≅
  AddCommGroup.of (direct_sum α $ λ i, (X i).val.obj (op S.val)) :=
let φ : α → AddCommGroup.{u+1} := λ i, (X i).val.obj (op S.val) in
sigma_eval_iso _ _ ≪≫
(colimit.is_colimit (discrete.functor φ)).cocone_point_unique_up_to_iso
  (AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1} φ)

lemma ι_sigma_eval_iso_direct_sum {α : Type (u+1)} (X : α → Condensed.{u} Ab.{u+1})
  (S : ExtrDisc.{u}) (i : α) :
  (sigma.ι X i : X i ⟶ _).val.app (op S.val) ≫ (sigma_eval_iso_direct_sum X S).hom =
  direct_sum.of _ i :=
begin
  dsimp only [sigma_eval_iso_direct_sum],
  erw ι_sigma_eval_iso_assoc, erw colimit.ι_desc, refl,
end

instance mono_coproduct_to_coproduct :
  mono (coproduct_to_coproduct F - 𝟙 _) :=
sorry

end Condensed
