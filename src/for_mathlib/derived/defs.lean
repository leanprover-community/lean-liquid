import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category
import category_theory.abelian.projective

noncomputable theory

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

universes v u
variables {A : Type u} [category.{v} A] [abelian A]

namespace homotopy_category

variables {ι : Type*} {c : complex_shape ι}

local notation `𝒦` := homotopy_category A c

/-- Say `c` is a complex shape on an index type `ι`. An object of `homotopy_category A c`
is acyclic if the homology of this object is 0 at all indices `i : ι`. -/
class is_acyclic (X : 𝒦) : Prop :=
(cond [] : ∀ i, is_zero ((homotopy_category.homology_functor _ _ i).obj X))

lemma is_acyclic_of_iso {X Y : 𝒦} (e : X ≅ Y) [is_acyclic X] : is_acyclic Y :=
begin
  constructor,
  intros i,
  let e' : (homology_functor A c i).obj X ≅ (homology_functor A c i).obj Y :=
    functor.map_iso _ e,
  apply is_zero_of_iso_of_zero _ e',
  apply is_acyclic.cond X i,
end

/-- An object of `homotopy_category A c` is "K-projective" if the only map from
that object to any acyclic object is the zero map. -/
class is_K_projective (X : 𝒦) : Prop :=
(cond [] : ∀ (Y : 𝒦) [is_acyclic Y] (f : X ⟶ Y), f = 0)

/-- A morphism in the homotopy category is a quasi-isomorphism if it
induces isomorphisms on all homology groups. -/
class is_quasi_iso {X Y : 𝒦} (f : X ⟶ Y) : Prop :=
(cond [] : ∀ i, is_iso ((homotopy_category.homology_functor _ _ i).map f))

end homotopy_category

namespace homotopy_category

local notation `𝒦` := homotopy_category A (complex_shape.up ℤ)
local notation `HH` := homotopy_category.homology_functor A (complex_shape.up ℤ) 0

/-- An object `(Cⁱ)` of `homotopy_category A ℤ↑` is bounded_by `n : ℕ` if the all the objects
`Cⁱ` for `i ≥ n` in the complex are zero -/
def bounded_by (X : 𝒦) (n : ℤ) : Prop :=
∀ i, n ≤ i → is_zero (X.as.X i)

class is_bounded_above (X : 𝒦) : Prop  :=
(cond [] : ∃ a : ℤ, X.bounded_by a)

class is_uniformly_bounded_above {α : Type*} (X : α → 𝒦) : Prop :=
(cond [] : ∃ n : ℤ, ∀ a, (X a).bounded_by n)

instance is_bounded_above_of_is_uniformly_bounded_above {α : Type*} (X : α → 𝒦)
  [is_uniformly_bounded_above X] (a) : is_bounded_above (X a) :=
begin
  obtain ⟨n,hn⟩ := is_uniformly_bounded_above.cond X,
  exact ⟨⟨n, hn a⟩⟩,
end

end homotopy_category

variables (A)

/-- The category `bounded_homotopy_category A` has objects the complexes indexed by `ℤ↑`
which are bounded above, i.e. the objects in the complex are equal to zero for sufficiently
large indices. Morphisms are homotopy classes of maps. -/
structure bounded_homotopy_category :=
(val : homotopy_category A (complex_shape.up ℤ))
[bdd : homotopy_category.is_bounded_above val]
