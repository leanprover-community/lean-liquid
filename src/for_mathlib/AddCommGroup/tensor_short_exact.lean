import for_mathlib.AddCommGroup.tensor
import for_mathlib.AddCommGroup
import for_mathlib.preserves_exact

noncomputable theory

universes u
open_locale tensor_product

open category_theory

namespace AddCommGroup

variables (A : AddCommGroup)

instance tensor_functor_additive : (tensor_functor.obj A).additive :=
{ map_add' := λ X Y f g, begin
    dsimp [map_tensor], ext x,
    dsimp only [linear_map.to_add_monoid_hom_coe, add_monoid_hom.add_apply],
    rw [← linear_map.add_apply],
    congr' 1, apply tensor_product.ext', intros x y,
    apply tensor_product.tmul_add,
  end }

instance tensor_flip_additive : functor.additive
  (tensor_functor.flip.obj A) :=
{ map_add' := λ X Y f g, begin
    dsimp [map_tensor], ext x,
    dsimp only [linear_map.to_add_monoid_hom_coe, add_monoid_hom.add_apply],
    rw [← linear_map.add_apply],
    congr' 1, apply tensor_product.ext', intros x y,
    apply tensor_product.add_tmul,
  end }

variables [no_zero_smul_divisors ℤ A]

instance tensor_functor_preserves_finite_limits :
  limits.preserves_finite_limits (tensor_functor.obj A) :=
sorry

lemma tensor_short_exact {X Y Z : AddCommGroup}
  (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : short_exact f g) :
  short_exact (map_tensor (𝟙 A) f) (map_tensor (𝟙 A) g) :=
(tensor_functor.obj A).map_short_exact f g hfg

end AddCommGroup
