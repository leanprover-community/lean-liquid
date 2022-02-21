import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category
import for_mathlib.derived.homological

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

namespace homological_complex
universes v u
variables {A : Type u} [category.{v} A] [abelian A]

local notation `𝒦` := homotopy_category A (complex_shape.up ℤ)
local notation `HH` := homotopy_category.homology_functor A (complex_shape.up ℤ) 0

class is_acyclic (X : 𝒦) : Prop :=
(cond : ∀ i, is_zero ((homotopy_category.homology_functor _ _ i).obj X))

class is_K_projective (X : 𝒦) : Prop :=
(cond : ∀ (Y : 𝒦) [is_acyclic Y] (f : X ⟶ Y), f = 0)

class is_quasi_iso {X Y : 𝒦} (f : X ⟶ Y) : Prop :=
(cond : ∀ i, is_iso ((homotopy_category.homology_functor _ _ i).map f))

-- Move this
instance homology_functor_additive : functor.additive HH := functor.additive.mk $
begin
  rintros X Y ⟨f⟩ ⟨g⟩,
  dsimp [homotopy_category.homology_functor],
  erw ← (homology_functor _ _ _).map_add,
  refl,
  apply_instance,
end

instance homology_functor_homological : homological_functor HH := sorry

/--
If `A → B → C → A[1]` is a distinguished triangle, and `A → B` is a quasi-isomorphism,
then `C` is acyclic.
-/
lemma is_acyclic_of_dist_triang_of_is_quasi_iso (T : triangle 𝒦) (hT : T ∈ dist_triang 𝒦)
  [is_quasi_iso T.mor₁] : is_acyclic T.obj₃ := sorry

lemma hom_K_projective_bijective {X Y : 𝒦} (P : 𝒦) [is_K_projective P]
  (f : X ⟶ Y) [is_quasi_iso f] : function.bijective (λ e : P ⟶ X, e ≫ f) :=
begin
  /-
  Steps:
  1. Complete `f` to a dist triang `X → Y → Z → X[1]`.
  2. Use LES assoc. to `Hom(P,-)`, proved in `for_mathlib/derived/homological.lean`.
  3. Use lemma above + def of K-projective to see that `Hom(P,Z) = 0`.
  -/
  sorry
end

end homological_complex
