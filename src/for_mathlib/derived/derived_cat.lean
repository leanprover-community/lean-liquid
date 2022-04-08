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

@[simps]
def has_shift_functor (i : ℤ) : bounded_derived_category A ⥤ bounded_derived_category A:=
{ obj := λ X,
  { val := X.val⟦i⟧,
    proj := by { dsimp, apply_instance } },
  map := λ X Y f, ⟨f.val⟦i⟧'⟩,
  map_id' := λ X, by { ext1, dsimp, apply category_theory.functor.map_id },
  map_comp' := λ X Y Z f g, by { ext1, dsimp, apply category_theory.functor.map_comp } }

section
open homological_complex

noncomputable
def has_shift_ε : 𝟭 (bounded_derived_category A) ≅ has_shift_functor A 0 :=
{ hom :=
  { app := λ X, ⟨(shift_zero _ _).inv⟩,
    naturality' := λ X Y f,
      by { ext1, apply (homotopy_category.shift_ε _).hom.naturality _, }, },
  inv :=
  { app := λ X, ⟨(shift_zero _ _).hom⟩,
    naturality' := λ X Y f,
      by { ext1, sorry, }, }, }

@[simps]
noncomputable
def has_shift_μ (m n : ℤ) : has_shift_functor A m ⋙ has_shift_functor A n ≅ has_shift_functor A (m + n) :=
{ hom :=
  { app := λ X, ⟨(shift_add _ _ _).inv⟩,
    naturality' := λ X Y f,
      by { ext1, exact (homotopy_category.shift_functor_add A m n).hom.naturality f.val, } },
  inv :=
  { app := λ X, ⟨(shift_add _ _ _).hom⟩,
    naturality' := begin intros, ext1, dsimp, have := (homotopy_category.shift_functor_add A m n).inv.naturality f.val,
      -- why doesn't this work?
      -- exact this,
      sorry
       end }, }

noncomputable
instance has_shift : has_shift (bounded_derived_category A) ℤ := has_shift_mk _ _ $
{ F := λ i, has_shift_functor A i,
  ε := has_shift_ε A,
  μ := has_shift_μ A,
  associativity := begin intros, ext, dsimp, sorry, end,
  left_unitality := sorry,
  right_unitality := sorry }

end

@[simps]
instance preadditive : preadditive (bounded_derived_category A) :=
{ hom_group := λ P Q,
  { add := λ f g, ⟨f.val + g.val⟩,
    add_assoc := by { intros, ext, apply add_assoc },
    zero := ⟨0⟩,
    zero_add := by { intros, ext, apply zero_add },
    add_zero := by { intros, ext, apply add_zero },
    nsmul := λ n f, ⟨n • f.val⟩,
    nsmul_zero' := by { intros f, ext, refine add_comm_monoid.nsmul_zero' f.val, },
    nsmul_succ' := by { intros n f, ext, exact add_comm_monoid.nsmul_succ' _ f.val },
    neg := λ f, ⟨-f.val⟩,
    sub := λ f g, ⟨f.val - g.val⟩,
    sub_eq_add_neg := by { intros, ext, apply sub_eq_add_neg },
    zsmul := λ n f, ⟨n • f.val⟩,
    zsmul_zero' := by { intros f, ext, apply add_comm_group.zsmul_zero' f.val },
    zsmul_succ' := by { intros n f, ext, apply add_comm_group.zsmul_succ' _ f.val },
    zsmul_neg' := by { intros n f, ext, apply add_comm_group.zsmul_neg' _ f.val },
    add_left_neg := by { intros, ext, apply add_left_neg },
    add_comm := by { intros, ext, apply add_comm } },
  add_comp' :=
    by { intros P Q R f₁ f₂ g, ext, apply preadditive.add_comp _ _ _ f₁.val f₂.val g.val },
  comp_add' :=
    by { intros P Q R f g₁ g₂, ext, apply preadditive.comp_add _ _ _ f.val g₁.val g₂.val } }

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
      (f : T ≅ replace_triangle S), true },
  isomorphic_distinguished := begin
    rintro T₁ ⟨S₁, hS₁, f₁, hf₁⟩ T₂ i, resetI,
    refine ⟨S₁, hS₁, i ≪≫ f₁, trivial⟩,
  end,
  contractible_distinguished := begin
    intro X,
    refine ⟨contractible_triangle _ X.val, pretriangulated.contractible_distinguished _, _⟩,
    sorry,
  end,
  distinguished_cocone_triangle := sorry,
  rotate_distinguished_triangle := sorry,
  complete_distinguished_triangle_morphism := sorry }

variable {A}
@[simps]
def lift {C : Type*} [category C] (F : bounded_homotopy_category A ⥤ C) :
  bounded_derived_category A ⥤ C :=
{ obj := λ X, F.obj X.val,
  map := λ X Y f, F.map f.val,
  map_id' := λ X, F.map_id _,
  map_comp' := λ X Y Z f g, F.map_comp _ _ }

noncomputable
def localize_lift {C : Type*} [category C]
  (F : bounded_homotopy_category A ⥤ C)
  [∀ (X Y : bounded_homotopy_category A) (f : X ⟶ Y)
    [h : is_quasi_iso f], is_iso (F.map f)] :
  localization_functor A ⋙ lift F ≅ F :=
nat_iso.of_components
(λ X, as_iso $ F.map X.π)
begin
  intros X Y f,
  dsimp,
  simp only [← F.map_comp],
  congr' 1,
  rw bounded_homotopy_category.lift_lifts,
end

@[simps]
noncomputable
def localization_iso (X : bounded_derived_category A) :
  (localization_functor A).obj X.val ≅ X :=
{ hom := ⟨X.val.π⟩,
  inv := ⟨bounded_homotopy_category.lift (𝟙 _) X.val.π⟩,
  hom_inv_id' := begin
    ext, dsimp, refine bounded_homotopy_category.lift_ext X.val.π _ _ _,
    rw [category.assoc, bounded_homotopy_category.lift_lifts, category.id_comp, category.comp_id],
  end,
  inv_hom_id' := by { ext, dsimp, rw bounded_homotopy_category.lift_lifts } }

noncomputable
def lift_unique {C : Type*} [category C]
  (F : bounded_homotopy_category A ⥤ C)
  [∀ (X Y : bounded_homotopy_category A) (f : X ⟶ Y)
    [h : is_quasi_iso f], is_iso (F.map f)]
  (G : bounded_derived_category A ⥤ C)
  (e : F ≅ localization_functor A ⋙ G) :
  lift F ≅ G :=
nat_iso.of_components
(λ X, e.app X.val ≪≫ G.map_iso (localization_iso _))
begin
  intros X Y f,
  simp only [lift_map, iso.trans_hom, iso.app_hom, functor.map_iso_hom, nat_trans.naturality_assoc,
    functor.comp_map, category.assoc, nat_iso.cancel_nat_iso_hom_left],
  rw [← functor.map_comp, ← functor.map_comp],
  congr' 1,
  ext,
  simp only [category_theory.category_comp_val, localization_functor_map_val,
    localization_iso_hom_val, bounded_homotopy_category.lift_lifts],
end

variable (A)
noncomputable
def Ext (n : ℤ) : (bounded_derived_category A)ᵒᵖ ⥤ bounded_derived_category A ⥤ Ab :=
functor.flip $ shift_functor _ n ⋙ preadditive_yoneda

@[simp]
lemma Ext_obj_obj (n : ℤ) (X : (bounded_derived_category A)ᵒᵖ) (Y : bounded_derived_category A) :
  ((Ext A n).obj X).obj Y = AddCommGroup.of (X.unop ⟶ Y⟦n⟧) := rfl

@[simp]
lemma Ext_map_app_apply (n : ℤ) {X Y : (bounded_derived_category A)ᵒᵖ}
  (f : X ⟶ Y) (Z : bounded_derived_category A) (e : ((Ext A n).obj X).obj Z) :
  ((Ext A n).map f).app Z e = f.unop ≫ e := rfl

@[simp]
lemma Ext_obj_map (n : ℤ) (X : (bounded_derived_category A)ᵒᵖ) {Y Z : bounded_derived_category A}
  (f : Y ⟶ Z) (e : ((Ext A n).obj X).obj Y) : ((Ext A n).obj X).map f e =
  e ≫ f⟦n⟧' := rfl

end bounded_derived_category

/-
0 → A → B → C → 0

A -f→ B → Cone(f) → A[1]

Canonical Cone(f) → C quasi iso

-/
