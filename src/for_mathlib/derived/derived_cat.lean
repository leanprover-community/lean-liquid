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
  use bounded_homotopy_category.lift Y.π (X.π ≫ f),
  split,
  { ext1, dsimp,
    apply bounded_homotopy_category.lift_ext (X.π ≫ f),
    simp only [category.assoc, bounded_homotopy_category.lift_lifts, category.comp_id,
      category.id_comp],
    apply_instance },
  { ext1, dsimp,
    apply bounded_homotopy_category.lift_ext Y.π,
    simp only [category.assoc, bounded_homotopy_category.lift_lifts, category.comp_id,
      category.id_comp],
    apply_instance }
end

local attribute [instance] limits.has_zero_object.has_zero

-- MOVE THIS
instance zero_is_K_projective : is_K_projective (0 : bounded_homotopy_category A).val :=
begin
  constructor,
  introsI Y _ f, ext,
end

noncomputable
instance has_zero_object : limits.has_zero_object (bounded_derived_category A) :=
{ zero := of 0,
  unique_to := λ X,
  { default := ⟨0⟩,
    uniq := λ a, by { ext1, cases a, dsimp at *, apply limits.has_zero_object.from_zero_ext } },
  unique_from := λ X,
  { default := ⟨0⟩,
    uniq := λ a, by { ext1, cases a, dsimp at *, apply limits.has_zero_object.to_zero_ext } } }

noncomputable
instance has_shift : has_shift (bounded_derived_category A) ℤ := has_shift_mk _ _ $
{ F := λ i,
  { obj := λ X,
    { val := X.val⟦i⟧,
      proj := by { dsimp, apply_instance } },
    map := λ X Y f, ⟨f.val⟦i⟧'⟩,
    map_id' := λ X, by { ext1, dsimp, apply category_theory.functor.map_id },
    map_comp' := λ X Y Z f g, by { ext1, dsimp, apply category_theory.functor.map_comp } },
  ε :=
  { hom :=
    { app := λ X, ⟨(shift_zero _ _).inv⟩,
      naturality' := sorry },
    inv :=
    { app := λ X, ⟨(shift_zero _ _).hom⟩,
      naturality' := sorry },
    hom_inv_id' := sorry,
    inv_hom_id' := sorry },
  μ := λ m n,
  { hom :=
    { app := λ X, ⟨(shift_add _ _ _).inv⟩,
      naturality' := sorry },
    inv :=
    { app := λ X, ⟨(shift_add _ _ _).hom⟩,
      naturality' := sorry },
    hom_inv_id' := sorry,
    inv_hom_id' := sorry },
  associativity := sorry,
  left_unitality := sorry,
  right_unitality := sorry }

@[simps]
instance preadditive : preadditive (bounded_derived_category A) :=
{ hom_group := λ P Q,
  { add := λ f g, ⟨f.val + g.val⟩,
    add_assoc := sorry,
    zero := ⟨0⟩,
    zero_add := sorry,
    add_zero := sorry,
    nsmul := λ n f, ⟨n • f.val⟩,
    nsmul_zero' := sorry,
    nsmul_succ' := sorry,
    neg := λ f, ⟨-f.val⟩,
    sub := λ f g, ⟨f.val - g.val⟩,
    sub_eq_add_neg := sorry,
    zsmul := λ n f, ⟨n • f.val⟩,
    zsmul_zero' := sorry,
    zsmul_succ' := sorry,
    zsmul_neg' := sorry,
    add_left_neg := sorry,
    add_comm := sorry },
  add_comp' := sorry,
  comp_add' := sorry }

instance additive (n : ℤ) : (shift_functor (bounded_derived_category A) n).additive :=
{ map_add' := begin
    intros P Q f g,
    ext1,
    dsimp,
    erw ← (shift_functor (bounded_homotopy_category A) n).map_add,
    refl,
  end }

open category_theory.triangulated

variable {A}
noncomputable
def replace_triangle (S : triangle (bounded_homotopy_category A)) :
  triangle (bounded_derived_category A) :=
{ obj₁ := of $ S.obj₁.replace,
  obj₂ := of $ S.obj₂.replace,
  obj₃ := of $ S.obj₃.replace,
  mor₁ := ⟨bounded_homotopy_category.lift (S.obj₁.π ≫ S.mor₁) S.obj₂.π⟩,
  mor₂ := ⟨bounded_homotopy_category.lift (S.obj₂.π ≫ S.mor₂) S.obj₃.π⟩,
  mor₃ := begin
    haveI : is_quasi_iso
      ((shift_functor (bounded_homotopy_category A) (1 : ℤ)).map S.obj₁.π) :=
    by { change is_quasi_iso ((S.obj₁.π)⟦(1 : ℤ)⟧'), by apply_instance }, -- WAT?
    exact ⟨bounded_homotopy_category.lift (S.obj₃.π ≫ S.mor₃) (S.obj₁.π⟦(1 : ℤ)⟧')⟩,
  end }

variable (A)
instance pretriangulated : triangulated.pretriangulated (bounded_derived_category A) :=
{ distinguished_triangles := { T |
    ∃ (S : triangle (bounded_homotopy_category A))
      (hS : S ∈ dist_triang (bounded_homotopy_category A))
      (f : T ⟶ replace_triangle S), is_iso f },
  isomorphic_distinguished := sorry,
  contractible_distinguished := sorry,
  distinguished_cocone_triangle := sorry,
  rotate_distinguished_triangle := sorry,
  complete_distinguished_triangle_morphism := sorry }

end bounded_derived_category
