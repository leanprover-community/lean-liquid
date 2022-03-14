import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category
import category_theory.abelian.projective

noncomputable theory

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

namespace homotopy_category

local notation `𝒦` := homotopy_category A (complex_shape.up ℤ)
local notation `HH` := homotopy_category.homology_functor A (complex_shape.up ℤ) 0

class is_acyclic (X : 𝒦) : Prop :=
(cond [] : ∀ i, is_zero ((homotopy_category.homology_functor _ _ i).obj X))

lemma is_acyclic_of_iso {X Y : 𝒦} (e : X ≅ Y) [is_acyclic X] : is_acyclic Y :=
begin
  constructor,
  intros i,
  let e' : (homology_functor A (complex_shape.up ℤ) i).obj X ≅
    (homology_functor A (complex_shape.up ℤ) i).obj Y :=
    functor.map_iso _ e,
  apply is_zero_of_iso_of_zero _ e',
  apply is_acyclic.cond X i,
end

class is_K_projective (X : 𝒦) : Prop :=
(cond [] : ∀ (Y : 𝒦) [is_acyclic Y] (f : X ⟶ Y), f = 0)

class is_quasi_iso {X Y : 𝒦} (f : X ⟶ Y) : Prop :=
(cond [] : ∀ i, is_iso ((homotopy_category.homology_functor _ _ i).map f))

class is_bounded_above (X : 𝒦) : Prop  :=
(cond [] : ∃ a : ℤ, ∀ i, a ≤ i → is_zero (X.as.X i))

end homotopy_category

variables (A)

structure bounded_homotopy_category :=
(val : homotopy_category A (complex_shape.up ℤ))
[bdd : homotopy_category.is_bounded_above val]
