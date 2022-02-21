import for_mathlib.homotopy_category_pretriangulated
import for_mathlib.abelian_category
import for_mathlib.derived.homological
import category_theory.abelian.projective

open category_theory category_theory.limits category_theory.triangulated
open homological_complex

namespace homotopy_category
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
  erw ← (_root_.homology_functor _ _ _).map_add,
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

variable [enough_projectives A]
noncomputable theory

-- Main theorem about existence of K-projective replacements.
-- Perhaps all we need is this for bounded complexes, in which case we should
-- add an additional typeclass parameter here.
theorem exists_K_projective_replacement (X : 𝒦) :
  ∃ (P : 𝒦) [is_K_projective P] (f : P ⟶ X), is_quasi_iso f := sorry

def replace (X : 𝒦) : 𝒦 := (exists_K_projective_replacement X).some

instance (X : 𝒦) : is_K_projective X.replace :=
(exists_K_projective_replacement X).some_spec.some

def π (X : 𝒦) : X.replace ⟶ X :=
(exists_K_projective_replacement X).some_spec.some_spec.some

instance (X : 𝒦) : is_quasi_iso X.π :=
(exists_K_projective_replacement X).some_spec.some_spec.some_spec

def lift {P X Y : 𝒦} [is_K_projective P] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] :
  P ⟶ X :=
((hom_K_projective_bijective P g).2 f).some

@[simp, reassoc]
lemma lift_lifts {P X Y : 𝒦} [is_K_projective P] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g] :
  lift f g ≫ g = f :=
((hom_K_projective_bijective P g).2 f).some_spec

lemma lift_unique {P X Y : 𝒦} [is_K_projective P] (f : P ⟶ Y) (g : X ⟶ Y) [is_quasi_iso g]
  (e : P ⟶ X) (h : e ≫ g = f) : e = lift f g :=
begin
  apply (hom_K_projective_bijective P g).1,
  simpa,
end

lemma lift_ext {P X Y : 𝒦} [is_K_projective P] (g : X ⟶ Y) [is_quasi_iso g]
  (a b : P ⟶ X) (h : a ≫ g = b ≫ g) : a = b :=
(hom_K_projective_bijective P g).1 h

end homotopy_category
