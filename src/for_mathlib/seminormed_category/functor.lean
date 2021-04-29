import data.real.basic
import for_mathlib.seminormed_category.basic
import category_theory.preadditive.additive_functor

namespace category_theory

namespace functor

class bounded_additive {C D : Type*} [category C] [category D] [semi_normed_category C] [semi_normed_category D]
  (F : C ⥤ D) extends functor.additive F : Prop :=
(bounded : ∃ c : ℝ, ∀ {X Y : C} (f : X ⟶ Y), ∥ F.map f ∥ ≤ c * ∥ f ∥)

end functor

end category_theory
