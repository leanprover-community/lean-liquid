import breen_deligne.apply_Pow

noncomputable theory

universes v

namespace breen_deligne

open category_theory category_theory.category category_theory.limits universal_map
  category_theory.preadditive

variables  {A₁ A₂ : Type*} [category.{v} A₁] [category.{v} A₂]
  [preadditive A₁] [preadditive A₂] [has_finite_biproducts A₁] [has_finite_biproducts A₂]
  (BD : data)
  (F₁ : A₁ ⥤ A₁) (F₂ : A₂ ⥤ A₂) {G G' : A₁ ⥤ A₂} [functor.additive G] [functor.additive G']
  (τ : G ⟶ G')
  (e : F₁ ⋙ G ≅ G ⋙ F₂) (e' : F₁ ⋙ G' ≅ G' ⋙ F₂)

lemma eval_Pow_functor_nat_trans_compatibility
  (h : e.hom ≫ whisker_right τ F₂ = whisker_left F₁ τ ≫ e'.hom) (M : A₁) (n : FreeMat) :
  τ.app (((eval_Pow_functor F₁).obj n).obj M) ≫ e'.hom.app _ ≫
    F₂.map ((apply_Pow G' n).hom.app M) =
  e.hom.app _ ≫ F₂.map ((apply_Pow G n).hom.app M) ≫
    ((eval_Pow_functor F₂).obj n).map (τ.app M) :=
begin
  dsimp only [eval_Pow_functor],
  have h₁ := nat_trans.congr_app h ((Pow n).obj M),
  simp only [nat_trans.comp_app, whisker_right_app, whisker_left] at h₁,
  slice_lhs 1 2 { erw ← h₁, },
  simp only [category.assoc],
  erw [← F₂.map_comp, ← F₂.map_comp],
  congr' 2,
  apply apply_Pow_naturality,
end

end breen_deligne
