import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

namespace homological_complex
universes v u
variables {A : Type u} [category.{v} A] [abelian A]

local notation `𝒦` := homotopy_category A (complex_shape.up ℤ)

class is_acyclic (X : 𝒦) : Prop :=
(cond : ∀ i, is_zero ((homotopy_category.homology_functor _ _ i).obj X))

class is_K_projective (X : 𝒦) : Prop :=
(cond : ∀ (Y : 𝒦) [is_acyclic Y] (f : X ⟶ Y), f = 0)

class is_quasi_iso {X Y : 𝒦} (f : X ⟶ Y) : Prop :=
(cond : ∀ i, is_iso ((homotopy_category.homology_functor _ _ i).map f))

end homological_complex
