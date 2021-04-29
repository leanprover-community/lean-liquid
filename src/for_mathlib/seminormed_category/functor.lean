import data.real.basic
import for_mathlib.seminormed_category.basic
import category_theory.preadditive.additive_functor

namespace category_theory

namespace functor

class norm_compat {C D : Type*} [category C] [category D] [semi_normed_category C]
  [semi_normed_category D] (F : C ⥤ D) : Prop :=
(norm_eq' [] : ∀ {X Y : C} (f : X ⟶ Y), ∥ F.map f ∥ = ∥ f ∥ . obviously)

restate_axiom norm_compat.norm_eq'
attribute [simp] norm_compat.norm_eq

end functor

end category_theory
