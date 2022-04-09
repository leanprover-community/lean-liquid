import for_mathlib.derived.K_projective

open category_theory

-- PR's as #13263
section

variables {C D : Type*} [category C] [category D]

lemma category_theory.functor.map_iso_injective (F : C ⥤ D) [faithful F] {X Y : C} :
  function.injective $ @functor.map_iso _ _ _ _ F X Y :=
λ i j h, iso.ext (functor.map_injective F (congr_arg iso.hom h : _))

def foo (F : C ⥤ D) [full F] [faithful F] {X Y : C} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) :=
equiv_of_fully_faithful F

/-- If `F` is fully faithful, we have an equivalence of hom-sets `X ≅ Y` and `F X ≅ F Y`. -/
@[simps]
def iso_equiv_of_fully_faithful (F : C ⥤ D) [full F] [faithful F] {X Y : C} : (X ≅ Y) ≃ (F.obj X ≅ F.obj Y) :=
{ to_fun := λ f, F.map_iso f,
  inv_fun := λ f, preimage_iso f,
  left_inv := λ f, by simp,
  right_inv := λ f, by { ext, simp, } }
end

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

variable (A)
def forget : bounded_derived_category A ⥤ bounded_homotopy_category A :=
{ obj := λ X, X.val,
  map := λ X Y f, f.val, }

variable {A}

@[simp] lemma forget_map_mk {X Y : bounded_derived_category A} (f : X.val ⟶ Y.val) :
  (forget A).map { val := f } = f :=
rfl

instance : faithful (forget A) := {}

instance : full (forget A) :=
{ preimage := λ X Y f, ⟨f⟩, }

variable {A}
@[simps]
def of (X : bounded_homotopy_category A) [homotopy_category.is_K_projective X.val] :
  bounded_derived_category A := { val := X }

@[simp] lemma forget_obj_of {X : bounded_homotopy_category A} [homotopy_category.is_K_projective X.val] :
  (forget A).obj (of X) = X :=
rfl

@[simps]
def mk_iso {X Y : bounded_derived_category A} (i : (forget A).obj X ≅ (forget A).obj Y) :
  X ≅ Y :=
{ hom := ⟨i.hom⟩,
  inv := ⟨i.inv⟩, }

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

@[simp]
lemma shift_functor_val (m : ℤ) {X Y : bounded_derived_category A} (f : X ⟶ Y) :
  ((shift_functor (bounded_derived_category A) m).map f).val =
    (shift_functor (bounded_homotopy_category A) m).map f.val :=
rfl

@[simps]
noncomputable
def shift_functor_forget (m : ℤ) :
  shift_functor (bounded_derived_category A) m ⋙ forget A ≅
    forget A ⋙ shift_functor (bounded_homotopy_category A) m :=
begin
  fapply nat_iso.of_components,
  { exact λ X, bounded_homotopy_category.mk_iso (by refl), },
  { intros,
    erw [category.id_comp, category.comp_id],
    refl, },
end

@[simps]
noncomputable
def shift_functor_localization_functor (m : ℤ) :
  shift_functor (bounded_homotopy_category A) m ⋙ localization_functor A ≅
    localization_functor A ⋙ shift_functor (bounded_derived_category A) m :=
begin
  fapply nat_iso.of_components,
  { intros,
    apply mk_iso,
    refine _ ≪≫ ((shift_functor_forget A m).app _).symm,
    dsimp,
    exact
    { hom := bounded_homotopy_category.lift ((shift_functor (bounded_homotopy_category A) m).obj X).π
        ((shift_functor (bounded_homotopy_category A) m).map X.π),
      inv := bounded_homotopy_category.lift ((shift_functor (bounded_homotopy_category A) m).map X.π)
        ((shift_functor (bounded_homotopy_category A) m).obj X).π, }, },
  { intros, ext, dsimp,
    simp only [bounded_homotopy_category.lift_comp_lift_self_assoc, category_theory.category.assoc],
    erw [category.comp_id, category.id_comp],
    simp [bounded_homotopy_category.shift_functor_map_lift], },
end

-- TODO replace this by pulling back a preadditive instance along `forget`?
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
  end }

variable (A)
@[simps]
noncomputable def forget_triangulated_functor_struct :
  triangulated.pretriangulated.triangulated_functor_struct
    (bounded_derived_category A) (bounded_homotopy_category A) :=
{ to_functor := forget A,
  comm_shift := nat_iso.of_components (λ X, by refl) (by tidy), }

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

@[simp, reassoc] lemma π_lift_id_π (X : bounded_derived_category A) :
  X.val.π ≫ bounded_homotopy_category.lift (𝟙 X.val) X.val.π = 𝟙 X.val.replace :=
begin
  refine bounded_homotopy_category.lift_ext X.val.π _ _ _,
  rw [category.assoc, bounded_homotopy_category.lift_lifts, category.id_comp, category.comp_id],
end

@[simps]
noncomputable
def localization_iso (X : bounded_derived_category A) :
  (localization_functor A).obj X.val ≅ X :=
{ hom := ⟨X.val.π⟩,
  inv := ⟨bounded_homotopy_category.lift (𝟙 _) X.val.π⟩, }

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

open category_theory.triangulated

variable {A}
@[simps obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
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

@[simps]
noncomputable
def replace_triangle_map {S T : triangle (bounded_homotopy_category A)} (f : S ⟶ T) :
  replace_triangle S ⟶ replace_triangle T :=
{ hom₁ := ⟨bounded_homotopy_category.lift (S.obj₁.π ≫ f.hom₁) T.obj₁.π⟩,
  hom₂ := ⟨bounded_homotopy_category.lift (S.obj₂.π ≫ f.hom₂) T.obj₂.π⟩,
  hom₃ := ⟨bounded_homotopy_category.lift (S.obj₃.π ≫ f.hom₃) T.obj₃.π⟩,
  comm₁' := by { ext, dsimp, simp only [triangle_morphism.comm₁, category.assoc,
    bounded_homotopy_category.lift_comp_lift_comp], },
  comm₂' := by { ext, dsimp, simp only [triangle_morphism.comm₂, category.assoc,
    bounded_homotopy_category.lift_comp_lift_comp], },
  comm₃' := begin
    ext, dsimp,
    rw [bounded_homotopy_category.shift_functor_map_lift, category_theory.functor.map_comp,
      bounded_homotopy_category.lift_comp_lift_comp, bounded_homotopy_category.lift_comp_lift_comp,
      category.assoc, triangle_morphism.comm₃, category.assoc],
  end, }

.

lemma replace_triangle_map_id (X : triangle (bounded_homotopy_category A)) :
  replace_triangle_map (𝟙 X) = 𝟙 (replace_triangle X) :=
by tidy

lemma replace_triangle_map_comp {X Y Z : triangle (bounded_homotopy_category A)}
  (f : X ⟶ Y) (g : Y ⟶ Z) :
  replace_triangle_map (f ≫ g) = replace_triangle_map f ≫ replace_triangle_map g :=
by ext; tidy

noncomputable
def replace_triangle' : triangle (bounded_homotopy_category A) ⥤ triangle (bounded_derived_category A) :=
{ obj := replace_triangle,
  map := λ S T f, replace_triangle_map f,
  map_id' := replace_triangle_map_id,
  map_comp' := λ X Y Z f g, replace_triangle_map_comp f g, }

attribute [simps obj_obj₁ obj_obj₂ obj_obj₃ obj_mor₁ obj_mor₂ obj_mor₃] replace_triangle'
attribute [simps map_hom₁ map_hom₂ map_hom₃] replace_triangle'

noncomputable
def replace_triangle_rotate (S : triangle (bounded_homotopy_category A)) :
  (replace_triangle S).rotate ≅ replace_triangle S.rotate :=
begin
  fapply triangle.iso.of_components,
  exact iso.refl _,
  exact iso.refl _,
  exact ((shift_functor_localization_functor A 1).app S.obj₁).symm,
  { ext, dsimp, simp, },
  { ext, dsimp, erw [category.id_comp, category.id_comp], simp, },
  { ext, dsimp,
    simp only [bounded_homotopy_category.lift_neg, bounded_homotopy_category.lift_comp_lift_comp,
      preadditive.comp_neg, preadditive.neg_comp, neg_inj, category.assoc,
      category_theory.functor.map_id],
   erw [category.id_comp, category.comp_id],
   simp [bounded_homotopy_category.shift_functor_map_lift], },
end

@[simps]
noncomputable def forget_replace_triangle (S : triangle (bounded_homotopy_category A)) :
  (forget_triangulated_functor_struct A).map_triangle (replace_triangle S) ≅
    bounded_homotopy_category.replace_triangle S :=
begin
  fapply triangle.iso.of_components,
  apply iso.refl _,
  apply iso.refl _,
  apply iso.refl _,
  all_goals { dsimp, simp, },
end

variable (A)

def pretriangulated_distinguished_triangles :=
 { T |
    ∃ (S : triangle (bounded_homotopy_category A))
      (hS : S ∈ dist_triang (bounded_homotopy_category A))
      (f : T ≅ replace_triangle S), true }

variable {A}

lemma isomorphic_distinguished (T₁ : triangle (bounded_derived_category A))
  (m : T₁ ∈ pretriangulated_distinguished_triangles A)
  (T₂ : triangle (bounded_derived_category A)) (i : T₂ ≅ T₁) :
  T₂ ∈ pretriangulated_distinguished_triangles A :=
begin
  obtain ⟨S₁, hS₁, f₁, hf₁⟩ := m,
  exact ⟨S₁, hS₁, i ≪≫ f₁, trivial⟩,
end

lemma forget_replace_triangle_distinguished  (S : triangle (bounded_homotopy_category A))
  (m : S ∈ dist_triang (bounded_homotopy_category A)) :
  (forget_triangulated_functor_struct A).map_triangle (replace_triangle S) ∈ dist_triang (bounded_homotopy_category A) :=
pretriangulated.isomorphic_distinguished
  _ (bounded_homotopy_category.distinguished_replace_triangle S m)
  _ (forget_replace_triangle S)

lemma forget_distinguished_of_distinguished
  {T : triangle (bounded_derived_category A)} (m : T ∈ pretriangulated_distinguished_triangles A) :
  (forget_triangulated_functor_struct A).map_triangle T ∈ dist_triang (bounded_homotopy_category A) :=
begin
  obtain ⟨S, hS, f, -⟩ := m,
  -- This is a formal consequence of `forget_replace_triangle_distinguished`,
  -- but will be easier to state once #13262 lands.
  sorry
end

lemma pretriangulated_contractible_distinguished (X : bounded_derived_category A) :
  contractible_triangle (bounded_derived_category A) X ∈
    pretriangulated_distinguished_triangles A :=
begin
  refine ⟨contractible_triangle _ X.val, pretriangulated.contractible_distinguished _, ⟨_, trivial⟩⟩,
  symmetry,
  fapply triangle.iso.of_components,
  exact localization_iso X,
  exact localization_iso X,
  exact localization_iso 0,
  { ext, dsimp, simp, },
  { ext, },
  { apply (cancel_epi (localization_iso 0).inv).1, ext, apply_instance, },
end

@[simp]
lemma shift_functor_map_val (m : ℤ) {X Y : bounded_derived_category A} (f : X ⟶ Y) :
  ((shift_functor (bounded_derived_category A) m).map f).val =
    (shift_functor (bounded_homotopy_category A) m).map f.val :=
rfl

lemma pretriangulated_distinguished_cocone_triangle
  {X Y : bounded_derived_category A}
  (f : X ⟶ Y) :
  ∃ (Z : bounded_derived_category A) (g : Y ⟶ Z)
    (h : Z ⟶ (shift_functor (bounded_derived_category A) 1).obj X),
    triangle.mk (bounded_derived_category A) f g h ∈
      pretriangulated_distinguished_triangles A :=
begin
  obtain ⟨Z, g, h, m⟩ := pretriangulated.distinguished_cocone_triangle _ _ f.val,
  use (localization_functor A).obj Z,
  use (localization_iso Y).inv ≫ (localization_functor A).map g,
  refine ⟨(localization_functor A).map (h ≫ eq_to_hom (by refl)) ≫ (localization_iso _).hom, _⟩,
  refine ⟨_, m, ⟨_, trivial⟩⟩,
  symmetry,
  fapply triangle.iso.of_components,
  { exact localization_iso _, },
  { exact localization_iso _, },
  { exact iso.refl _, },
  { ext, dsimp, simp only [bounded_homotopy_category.lift_lifts], },
  { ext, dsimp,
    simp only [category.comp_id, bounded_derived_category.π_lift_id_π_assoc], },
  { ext, dsimp,
    simp only [category.comp_id, category.id_comp, bounded_homotopy_category.lift_lifts], },
end

lemma rotate_distinguished_triangle (T : triangle (bounded_derived_category A)) :
  T ∈ pretriangulated_distinguished_triangles A ↔
    T.rotate ∈ pretriangulated_distinguished_triangles A :=
begin
  split,
  { rintro ⟨S, hS, f, -⟩,
    use S.rotate,
    refine ⟨pretriangulated.rot_of_dist_triangle _ _ hS, _, trivial⟩,
    exact rotate.map_iso f ≪≫ replace_triangle_rotate _, },
  { rintro ⟨S, hS, f, -⟩,
    use S.inv_rotate,
    refine ⟨pretriangulated.inv_rot_of_dist_triangle _ _ hS, _, trivial⟩,

    let R := (rotate : triangle (bounded_derived_category A) ⥤ triangle (bounded_derived_category A)),
    haveI : faithful R := sorry, -- available after #13262
    haveI : full R := sorry, -- available after #13262
    apply (iso_equiv_of_fully_faithful R).inv_fun,
    refine f ≪≫ _ ≪≫ (replace_triangle_rotate _).symm,
    apply replace_triangle'.map_iso,
    exact (triangle_rotation).counit_iso.symm.app S, },
end

lemma complete_distinguished_triangle_morphism (T₁ T₂ : triangle (bounded_derived_category A))
    (m₁ : T₁ ∈ pretriangulated_distinguished_triangles A)
    (m₂ : T₂ ∈ pretriangulated_distinguished_triangles A)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
      (∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
        T₁.mor₃ ≫ (shift_functor (bounded_derived_category A) 1).map a = c ≫ T₂.mor₃) :=
begin
  -- We work formally, just using the fact this is true in the bounded homotopy category,
  -- without needing to care why.
  obtain ⟨c', h1, h2⟩ := pretriangulated.complete_distinguished_triangle_morphism
    ((forget_triangulated_functor_struct A).map_triangle T₁)
    ((forget_triangulated_functor_struct A).map_triangle T₂)
    (forget_distinguished_of_distinguished m₁)
    (forget_distinguished_of_distinguished m₂) ((forget A).map a) ((forget A).map b)
    (congr_arg bounded_derived_category_hom.val comm),
  use c',
  dsimp at h1 h2,
  split,
  { apply (forget A).map_injective,
    simpa only [(forget A).map_comp] using h1, },
  { apply (forget A).map_injective,
    simp only [category_theory.category.comp_id] at h2,
    simp only [(forget A).map_comp],
    exact h2, },
end

variable (A)

instance pretriangulated : triangulated.pretriangulated (bounded_derived_category A) :=
{ distinguished_triangles := pretriangulated_distinguished_triangles A,
  isomorphic_distinguished := isomorphic_distinguished,
  contractible_distinguished := pretriangulated_contractible_distinguished,
  distinguished_cocone_triangle := λ X Y f, pretriangulated_distinguished_cocone_triangle f,
  rotate_distinguished_triangle := rotate_distinguished_triangle,
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism, }

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
