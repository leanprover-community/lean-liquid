import for_mathlib.AddCommGroup.tensor
import for_mathlib.AddCommGroup

noncomputable theory

universes u
open_locale tensor_product

open category_theory

namespace AddCommGroup

lemma tensor_short_exact (A : AddCommGroup) [no_zero_smul_divisors ℤ A]
  {X Y Z : AddCommGroup} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : short_exact f g) :
  short_exact (AddCommGroup.map_tensor (𝟙 A) f) (AddCommGroup.map_tensor (𝟙 A) g) :=
sorry

end AddCommGroup
