import breen_deligne.eval

noncomputable theory

namespace category_theory
namespace preadditive
open category_theory category_theory.limits

universes v

variables {C D : Type*} [category.{v} C] [category.{v} D] [preadditive C] [preadditive D]
  [has_finite_biproducts C] [has_finite_biproducts D] (F : C ⥤ D) [functor.additive F] (n : ℕ)

@[simps]
def apply_Pow : Pow n ⋙ F ≅ F ⋙ Pow n := nat_iso.of_components (λ A,
  { hom := biproduct.lift (λ i, F.map (biproduct.π _ i)),
    inv := biproduct.desc (λ i, F.map (biproduct.ι _ i)),
    hom_inv_id' := by simpa only [biproduct.lift_desc, ← F.map_comp, ← F.map_sum,
      biproduct.total] using F.map_id _,
    inv_hom_id' := begin
      ext i j,
      by_cases i = j,
      { subst h,
        dsimp,
        simp only [biproduct.ι_desc_assoc, category.assoc, biproduct.lift_π,
          category.comp_id, biproduct.ι_π_self, ← F.map_comp, F.map_id], },
      { dsimp,
        simp only [biproduct.ι_desc_assoc, category.assoc, biproduct.lift_π,
          category.comp_id, ← F.map_comp, limits.biproduct.ι_π_ne _ h,
          functor.map_zero], },
    end, })
(λ X Y f, by { ext, simp only [category.assoc, biproduct.lift_π,
  functor.comp_map, Pow_map, biproduct.lift_map, ← F.map_comp, biproduct.map_π], })

open breen_deligne.universal_map

def eval_Pow_functor_comp {A₁ A₂ : Type*} [category A₁] [category A₂]
  [preadditive A₁] [preadditive A₂] [has_finite_biproducts A₁] [has_finite_biproducts A₂]
  (F₁ : A₁ ⥤ A₁) (F₂ : A₂ ⥤ A₂) (G : A₁ ⥤ A₂)
  [functor.additive G]
  (e : F₁ ⋙ G ≅ G ⋙ F₂) :
  eval_Pow_functor F₂ ⋙ ((whiskering_left _ _ A₂).obj G) ≅
  eval_Pow_functor F₁ ⋙ (whiskering_right A₁ _ _).obj G
:=
nat_iso.of_components
(λ n, begin
  apply iso.symm,
  refine (functor.associator _ _ _) ≪≫ iso_whisker_left _ e ≪≫ _,
  refine (functor.associator _ _ _).symm ≪≫ _ ≪≫ (functor.associator _ _ _),
  refine iso_whisker_right (apply_Pow G n) _,
end)
(λ n m f, begin
  ext M,
  dsimp only [whiskering_right, whiskering_left, functor.associator, iso.symm,
    iso_whisker_left, iso_whisker_right, iso.trans, nat_trans.comp_app,
    functor.map_iso, eval_Pow_functor, functor.comp_map, whisker_right, whisker_left],
  repeat { erw category.id_comp, },
  repeat { erw category.comp_id, },
  /- strategy : starting with slice_rhs 2 3, use a naturality property of `eval_Pow` with
  respect to the additive functor `G`, then the statement would only involve
  the functors `G` and `F₂`. -/
  sorry,
end)

end preadditive

end category_theory

namespace breen_deligne

namespace data

open category_theory category_theory.limits category_theory.preadditive
open universal_map

variables  {A₁ A₂ : Type*} [category A₁] [category A₂]
  [preadditive A₁] [preadditive A₂] [has_finite_biproducts A₁] [has_finite_biproducts A₂]
  (BD : data)
  (F₁ : A₁ ⥤ A₁) (F₂ : A₂ ⥤ A₂) (G : A₁ ⥤ A₂) [functor.additive G]
  (e : F₁ ⋙ G ≅ G ⋙ F₂)

instance additive_whiskering_left :
  functor.additive ((whiskering_left _ _ A₂).obj G) := { }
instance additive_whiskering_right :
  functor.additive ((whiskering_right A₁ _ _).obj G) := { }

include F₁ e
def eval_functor'_comp :
  (eval_functor' F₂ ⋙ ((whiskering_left _ _ A₂).obj G).map_homological_complex _ ≅
  eval_functor' F₁ ⋙ ((whiskering_right A₁ _ _).obj G).map_homological_complex _) :=
begin
-- use eval_Pow_functor_comp
  sorry,
end

end data

end breen_deligne
