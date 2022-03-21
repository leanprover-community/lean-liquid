import category_theory.monoidal.functor

open category_theory
variables {C D : Type*} [category C] [category D]
  [monoidal_category C] [monoidal_category D]

namespace category_theory.monoidal_functor

variables (F : monoidal_functor C D)

lemma map_associator_hom
  {X Y Z : C} : F.map (α_ X Y Z).hom =
  inv (F.μ (X ⊗ Y) Z) ≫
  inv (F.μ X Y ⊗ 𝟙 (F.obj Z)) ≫
  (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
  (𝟙 (F.obj X) ⊗ F.μ Y Z) ≫
  F.μ X (Y ⊗ Z) :=
begin
  rw [is_iso.eq_inv_comp, is_iso.eq_inv_comp],
  exact (F.to_lax_monoidal_functor.associativity X Y Z),
end

lemma map_associator_inv
  {X Y Z : C} : F.map (α_ X Y Z).inv =
  inv (F.μ X (Y ⊗ Z)) ≫
  inv (𝟙 (F.obj X) ⊗ F.μ Y Z) ≫
  (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫
  (F.μ X Y ⊗ 𝟙 (F.obj Z)) ≫
  (F.μ (X ⊗ Y) Z) :=
begin
  rw [is_iso.eq_inv_comp, is_iso.eq_inv_comp],
  exact (F.to_lax_monoidal_functor.associativity_inv X Y Z),
end

end category_theory.monoidal_functor
