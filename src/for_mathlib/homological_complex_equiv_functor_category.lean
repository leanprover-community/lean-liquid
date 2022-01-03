import algebra.homology.homological_complex

open category_theory category_theory.limits

namespace homological_complex

universes w' w v v' u u'

variables {V : Type u} [category.{v} V] {J : Type w} [category.{w'} J]
variables {ι : Type u'} {c : complex_shape ι}

--move this
lemma congr_f [has_zero_morphisms V] {X Y : homological_complex V c} {f g : X ⟶ Y}
  (h : f = g) (x : ι) : f.f x = g.f x := congr_arg _ h

-- move this
section
variables {C : Type u} [category.{v} C] {Z : C → Prop}
@[simps]
def lift_iso {X Y : { X : C // Z X }} (h : (X : C) ≅ Y) : X ≅ Y :=
{ hom := h.hom, inv := h.inv, hom_inv_id' := h.hom_inv_id, inv_hom_id' := h.inv_hom_id }
end

section walking_complex

@[nolint unused_arguments]
def walking_complex (c : complex_shape ι) := ι

inductive walking_complex_hom : walking_complex c → walking_complex c → Type u'
| id : Π i, walking_complex_hom i i
| d : Π {i j}, c.rel i j → walking_complex_hom i j
| zero : Π i j, walking_complex_hom i j

section

open walking_complex_hom

def walking_complex_hom_comp (i j k : walking_complex c) :
  walking_complex_hom i j → walking_complex_hom j k → walking_complex_hom i k :=
begin
  intros f g,
  cases f with _ _ _ r,
  { exact g },
  { cases g, exacts [walking_complex_hom.d r, zero _ _, zero _ _] },
  { exact zero _ _ },
end

instance : category_struct (walking_complex c) :=
{ hom := walking_complex_hom,
  id := walking_complex_hom.id,
  comp :=
  begin
    intros i j k f g,
    cases f with _ _ _ r,
    { exact g },
    { cases g, exacts [walking_complex_hom.d r, zero _ _, zero _ _] },
    { exact zero _ _ },
  end }
end

local attribute [tidy] tactic.case_bash

instance : category (walking_complex c) := {}
.

instance walking_complex_hom_has_zero (i j : walking_complex c) : has_zero (i ⟶ j) :=
⟨walking_complex_hom.zero i j⟩

instance : has_zero_morphisms (walking_complex c) := {}
.

@[simp] lemma walking_complex_hom_id (i : walking_complex c) : walking_complex_hom.id i = 𝟙 i :=
rfl
@[simp] lemma walking_complex_hom_zero (i : walking_complex c) : walking_complex_hom.zero i = 0 :=
rfl

def walking_complex_d {i j : walking_complex c} (r : c.rel i j) : i ⟶ j :=
  walking_complex_hom.d r

@[simp] lemma walking_complex_d_eq {i j : walking_complex c} (r : c.rel i j) :
  walking_complex_hom.d r = walking_complex_d r := rfl

@[simp] lemma walking_complex_hom_d_comp_d {i j k : walking_complex c}
  (r : c.rel i j) (r' : c.rel j k) : walking_complex_d r ≫ walking_complex_d r' = 0 := rfl

variable [has_zero_morphisms V]

def complex_to_functor_map
  (h : homological_complex V c) {i j : walking_complex c} (f : i ⟶ j) : h.X i ⟶ h.X j :=
begin
  cases f, exacts [𝟙 _, h.d _ _, 0]
end

@[simp]
lemma complex_to_functor_map_id
  (h : homological_complex V c) (i : walking_complex c) : complex_to_functor_map h (𝟙 i) = 𝟙 _ :=
rfl

@[simp]
lemma complex_to_functor_map_zero
  (h : homological_complex V c) (i j : walking_complex c) :
    complex_to_functor_map h (0 : i ⟶ j) = 0 :=
rfl

@[simp]
lemma complex_to_functor_map_d
  (h : homological_complex V c) {i j : walking_complex c} (r : c.rel i j) :
    complex_to_functor_map h (walking_complex_d r) = h.d _ _ := rfl

@[simps]
def complex_to_functor (h : homological_complex V c) :
  walking_complex c ⥤ V :=
{ obj := h.X, map := λ i j f, complex_to_functor_map h f }
.

variable [decidable_rel c.rel]

@[simps]
def functor_to_complex (F : walking_complex c ⥤ V)
  (hF : ∀ i j, F.map (0 : i ⟶ j) = 0) :
  homological_complex V c :=
{ X := F.obj,
  d := λ i j, if r : c.rel i j then F.map (walking_complex_d r) else 0,
  d_comp_d' := by { introv r r',
    rw [dif_pos r, dif_pos r', ← F.map_comp, walking_complex_hom_d_comp_d, hF] } }
.
variables (c V)

@[simps]
def complex_to_functor_functor :
  homological_complex V c ⥤ { F : walking_complex c ⥤ V // ∀ i j, F.map (0 : i ⟶ j) = 0 } :=
{ obj := λ X, ⟨complex_to_functor X, λ _ _, rfl⟩, map := λ X Y f, { app := f.f } }

@[simps]
def functor_to_complex_functor :
  { F : walking_complex c ⥤ V // ∀ i j, F.map (0 : i ⟶ j) = 0 } ⥤ homological_complex V c :=
{ obj := λ F, functor_to_complex F.1 F.2,
  map := λ F G f, { f := f.app, comm' := by { intros i j r, simp [dif_pos r] } } }
.

@[simps]
def complex_equiv_functor_unit :
  𝟭 _ ≅ complex_to_functor_functor V c ⋙ functor_to_complex_functor V c :=
nat_iso.of_components
  (λ X, hom.iso_of_components (λ i, iso.refl _) (by { introv r, dsimp, simp [if_pos r] }))
  (by { intros, ext, dsimp, simp })

@[simps]
def complex_equiv_functor_counit :
  functor_to_complex_functor V c ⋙ complex_to_functor_functor V c ≅ 𝟭 _ :=
nat_iso.of_components
  (λ F, lift_iso $ nat_iso.of_components (λ i, iso.refl _)
    (by { introv, cases F with F hF, cases f; dsimp; simp [*, hF] }))
  (by { introv, ext, dsimp, erw [nat_trans.comp_app, nat_trans.comp_app], dsimp, simp })

@[simps]
def complex_equiv_functor :
  homological_complex V c ≌ { F : walking_complex c ⥤ V // ∀ i j, F.map (0 : i ⟶ j) = 0 } :=
{ functor := complex_to_functor_functor V c,
  inverse := functor_to_complex_functor V c,
  unit_iso := complex_equiv_functor_unit V c,
  counit_iso := complex_equiv_functor_counit V c,
  functor_unit_iso_comp' :=
    by { intro x, ext, erw [nat_trans.comp_app, nat_trans.id_app], dsimp, simp } }
.

instance : is_equivalence (complex_to_functor_functor V c) :=
is_equivalence.of_equivalence (complex_equiv_functor V c)
instance : is_equivalence (functor_to_complex_functor V c) :=
is_equivalence.of_equivalence_inverse (complex_equiv_functor V c)

@[simps, derive [full, faithful]]
def complex_to_functor_category_functor : homological_complex V c ⥤ walking_complex c ⥤ V :=
complex_to_functor_functor V c ⋙ induced_functor _

end walking_complex

section walking_preadditive_complex

/-
TODO : If `V` is preadditive, then the cateogory of homological complexes is equivalent to the
category of additive functors from a preadditive category `walking_preadditive_complex` to `V`.
-/

end walking_preadditive_complex

end homological_complex
