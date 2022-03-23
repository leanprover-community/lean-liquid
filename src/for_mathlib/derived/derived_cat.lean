import for_mathlib.derived.K_projective

open category_theory
variables (A : Type*) [category A] [abelian A] [enough_projectives A]

structure bounded_derived_category extends bounded_homotopy_category A :=
[proj : homotopy_category.is_K_projective val]

namespace bounded_derived_category

instance (X : bounded_derived_category A) : homotopy_category.is_K_projective X.val := X.proj

@[simps]
instance : category (bounded_derived_category A) :=
{ hom := λ X Y, X.to_bounded_homotopy_category ⟶ Y.to_bounded_homotopy_category,
  id := λ X, 𝟙 X.to_bounded_homotopy_category,
  comp := λ X Y Z f g, f ≫ g,
  id_comp' := λ X Y f, category.id_comp _,
  comp_id' := λ X Y f, category.comp_id _,
  assoc' := λ X Y Z W f g h, category.assoc _ _ _ }

variable {A}
def of (X : bounded_homotopy_category A) [homotopy_category.is_K_projective X.val] :
  bounded_derived_category A := {..X}

variable (A)
@[simps]
noncomputable def localization_functor :
  bounded_homotopy_category A ⥤ bounded_derived_category A :=
{ obj := λ X, of $ X.replace,
  map := λ X Y f, bounded_homotopy_category.lift (X.π ≫ f) Y.π,
  map_id' := begin
    intros X, symmetry, apply bounded_homotopy_category.lift_unique,
    dsimp, simp only [category.id_comp, category.comp_id],
  end,
  map_comp' := begin
    intros X Y Z f g,
    symmetry, apply bounded_homotopy_category.lift_unique,
    dsimp, simp only [category.assoc, bounded_homotopy_category.lift_lifts,
      bounded_homotopy_category.lift_lifts_assoc],
  end }

end bounded_derived_category
