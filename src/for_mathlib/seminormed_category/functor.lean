import data.real.basic
import for_mathlib.seminormed_category.basic
import category_theory.preadditive.additive_functor

namespace category_theory

namespace functor

def bounded_by {C D : Type*} [category C] [category D] [semi_normed_category C]
  [semi_normed_category D] (F : C ⥤ D) (c : ℝ) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), ∥ F.map f ∥ ≤ c * ∥ f ∥

class bounded_additive {C D : Type*} [category C] [category D] [semi_normed_category C]
  [semi_normed_category D] (F : C ⥤ D) extends functor.additive F : Prop :=
(bounded [] : ∃ c : ℝ, F.bounded_by c)

noncomputable def norm {C D : Type*} [category C] [category D] [semi_normed_category C]
  [semi_normed_category D] (F : C ⥤ D) [bounded_additive F] : ℝ :=
Inf {a | F.bounded_by a}

lemma norm_nonneg {C D : Type*} [category C] [category D] [semi_normed_category C]
  [semi_normed_category D] (F : C ⥤ D) [bounded_additive F] : 0 ≤ F.norm := sorry

lemma le_norm {C D : Type*} [category C] [category D] [semi_normed_category C]
  [semi_normed_category D] {X Y : C} (F : C ⥤ D) [bounded_additive F] (f : X ⟶ Y) :
  ∥ F.map f ∥ ≤ F.norm * ∥ f ∥ := sorry

end functor

end category_theory
