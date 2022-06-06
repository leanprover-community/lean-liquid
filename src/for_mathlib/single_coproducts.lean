import for_mathlib.derived.ext_coproducts

.

open category_theory
open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

namespace bounded_homotopy_category

instance uniformly_bounded_single {α : Type v} (i : ℤ) (X : α → A) :
  uniformly_bounded (λ a : α, (single A i).obj (X a)) := sorry

instance preserves_coproducts_single {α : Type v} (i : ℤ) :
  preserves_colimits_of_shape (discrete α) (single A i) := sorry

variables [enough_projectives A]

instance preserves_coproducts_Ext' {α : Type v} (i : ℤ) (Y : A) :
  preserves_limits_of_shape (discrete α)
  ((Ext' i).flip.obj Y) := sorry

end bounded_homotopy_category
