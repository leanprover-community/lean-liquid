import category_theory.derived

import for_mathlib.snake_lemma
import for_mathlib.delta_functor

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory

variables {C : Type u} [category.{v} C] {D : Type*} [category D]

-- Importing `category_theory.abelian.projective` and assuming
-- `[abelian C] [enough_projectives C] [abelian D]` suffices to acquire all the following:
variables [preadditive C] [has_zero_object C] [has_equalizers C]
variables [has_images C] [has_projective_resolutions C]
variables [preadditive D] [has_zero_object D] [has_equalizers D] [has_cokernels D]
variables [has_images D] [has_image_maps D]

instance (F : C ⥤ D) [F.additive] : delta_functor F.left_derived :=
{ δ := _,
  mono := _,
  exact' := _,
  exact_δ := _,
  δ_exact := _ }

end category_theory
