import category_theory.differential_object
import category_theory.pi.basic

universes w w₁ w₂ v v₁ v₂ u u₁ u₂

open category_theory.limits

/-! Some results in category theory that don't exist (or at least, that I couldn't find) yet.
 This should maybe be split up in different files. -/

namespace category_theory

namespace differential_object

variables {C : Type u₁} [category.{v₁} C] [has_zero_morphisms C] [has_shift C]
          {D : Type u₂} [category.{v₂} D] [has_zero_morphisms D] [has_shift D]
  {X Y Z : differential_object C}

end differential_object

end category_theory
