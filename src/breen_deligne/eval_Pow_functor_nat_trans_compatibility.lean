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
  sorry
end

end breen_deligne
