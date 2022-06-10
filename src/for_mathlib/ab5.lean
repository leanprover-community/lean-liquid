import for_mathlib.exact_functor
import for_mathlib.ab4
import for_mathlib.abelian_sheaves.functor_category

namespace category_theory

open category_theory.limits

universes v u
variables (A : Type u) [category.{v} A] [abelian A] [has_colimits A]

instance colim_additive (J : Type v) [small_category J]:
  functor.additive (limits.colim : ((J ⥤ A) ⥤ A)) := ⟨⟩ .

class AB5 : Prop :=
(cond [] : ∀ (J : Type v) [small_category J] [is_filtered J],
  functor.exact (limits.colim : (J ⥤ A) ⥤ A))

end category_theory
