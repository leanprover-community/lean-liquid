import for_mathlib.derived.K_projective

open category_theory
variables (A : Type*) [category A] [abelian A] [enough_projectives A]

structure bounded_derived_category :=
(val : bounded_homotopy_category A)
[proj : homotopy_category.is_K_projective val.val]

variable {A}
@[ext]
structure bounded_derived_category_hom (X Y : bounded_derived_category A) :=
(val : X.val ⟶ Y.val)

namespace bounded_derived_category

instance (X : bounded_derived_category A) : homotopy_category.is_K_projective X.val.val := X.proj

@[simps]
instance : category (bounded_derived_category A) :=
{ hom := λ X Y, bounded_derived_category_hom X Y,
  id := λ X, ⟨𝟙 X.val⟩,
  comp := λ X Y Z f g, ⟨f.val ≫ g.val⟩,
  id_comp' := λ X Y f, by { ext1, apply category.id_comp _ },
  comp_id' := λ X Y f, by { ext1, apply category.comp_id _ },
  assoc' := λ X Y Z W f g h, by { ext1, apply category.assoc _ _ _ } }

variable {A}
@[simps]
def of (X : bounded_homotopy_category A) [homotopy_category.is_K_projective X.val] :
  bounded_derived_category A := { val := X }

variable (A)
@[simps]
noncomputable def localization_functor :
  bounded_homotopy_category A ⥤ bounded_derived_category A :=
{ obj := λ X, of $ X.replace,
  map := λ X Y f, ⟨bounded_homotopy_category.lift (X.π ≫ f) Y.π⟩,
  map_id' := begin
    intros X, symmetry, ext1, apply bounded_homotopy_category.lift_unique,
    dsimp, simp only [category.id_comp, category.comp_id],
  end,
  map_comp' := begin
    intros X Y Z f g,
    symmetry, ext1, apply bounded_homotopy_category.lift_unique,
    dsimp, simp only [category.assoc, bounded_homotopy_category.lift_lifts,
      bounded_homotopy_category.lift_lifts_assoc],
  end }

open homotopy_category

lemma is_iso_localization_functor_map_of_is_quasi_iso
  (X Y : bounded_homotopy_category A) (f : X ⟶ Y)
  [is_quasi_iso f] : is_iso ((localization_functor _).map f) :=
begin
  haveI : is_quasi_iso (X.π ≫ f),
  { have := homotopy_category.is_quasi_iso_comp_iso,

   },
  let e : Y.replace ⟶ X.replace := bounded_homotopy_category.lift Y.π (X.π ≫ f),
  use e,
  split,
  { ext1, dsimp [e],
    apply bounded_homotopy_category.lift_ext (X.π ≫ f),
    simp only [category.assoc, bounded_homotopy_category.lift_lifts, category.comp_id,
      category.id_comp],
    apply_instance },
  { ext1, dsimp [e],
    apply bounded_homotopy_category.lift_ext Y.π,
    simp only [category.assoc, bounded_homotopy_category.lift_lifts, category.comp_id,
      category.id_comp],
    apply_instance }
end

end bounded_derived_category
