import category_theory.limits.filtered_colimit_commutes_finite_limit
import for_mathlib.preserves_finite_limits

import for_mathlib.AddCommGroup.tensor
import for_mathlib.AddCommGroup
import for_mathlib.preserves_exact

noncomputable theory

universes u
open_locale tensor_product

open category_theory

namespace AddCommGroup

variables (A : AddCommGroup)

variables [no_zero_smul_divisors ℤ A]

instance tensor_functor_preserves_finite_limits :
  limits.preserves_finite_limits (tensor_functor.obj A) :=
preserves_finite_limits_of_preserves_mono_preserves_finite_colimits _ $
λ X Y f hf, by { resetI, apply_instance }

lemma tensor_short_exact {X Y Z : AddCommGroup}
  (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : short_exact f g) :
  short_exact (map_tensor (𝟙 A) f) (map_tensor (𝟙 A) g) :=
(tensor_functor.obj A).map_short_exact f g hfg

end AddCommGroup
