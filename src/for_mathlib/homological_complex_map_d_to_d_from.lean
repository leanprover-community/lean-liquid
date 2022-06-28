import algebra.homology.homological_complex
import algebra.homology.additive

noncomputable theory

universes v

open category_theory category_theory.limits

namespace category_theory

namespace functor

section preadditive

variables {C D : Type*} [category C] [preadditive C] [category D] [preadditive D]
variables [has_zero_object C] [has_zero_object D]
variables {M : Type*} {c : complex_shape M}
variables (F : C ⥤ D) [functor.additive F] (X : homological_complex C c)

/-@[simp]
def obj_prev_X {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i : M) :
  F.obj (X.X_prev i) ≅ ((F.map_homological_complex c).obj X).X_prev i :=
begin
  rcases h : c.prev i with _ | ⟨j, hij⟩,
  { exact F.map_iso (homological_complex.X_prev_iso_zero X h) ≪≫ (map_zero_object F) ≪≫
      (homological_complex.X_prev_iso_zero _ h).symm, },
  { exact F.map_iso (homological_complex.X_prev_iso X hij) ≪≫ (by refl) ≪≫
    (homological_complex.X_prev_iso _ hij).symm, },
end

@[simp]
def obj_X_next {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i : M) :
  F.obj (X.X_next i) ≅ ((F.map_homological_complex c).obj X).X_next i :=
begin
  rcases h : c.next i with _ | ⟨j, hij⟩,
  { exact F.map_iso (homological_complex.X_next_iso_zero X h) ≪≫ (map_zero_object F) ≪≫
      (homological_complex.X_next_iso_zero _ h).symm, },
  { exact F.map_iso (homological_complex.X_next_iso X hij) ≪≫ (by refl) ≪≫
    (homological_complex.X_next_iso _ hij).symm, },
end-/

def map_d_to₁ (i : M) (h : c.prev i = none) :
  arrow.mk (F.map (X.d_to i)) ≅ arrow.mk (((F.map_homological_complex c).obj X).d_to i) :=
arrow.iso_mk (F.map_iso (homological_complex.X_prev_iso_zero X h) ≪≫
  map_zero_object F ≪≫ (homological_complex.X_prev_iso_zero _ h).symm) (iso.refl _)
begin
  dsimp,
  simp only [zero_comp, comp_zero, category.comp_id, X.d_to_eq_zero h, F.map_zero],
end

def map_d_to₂ {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i j : M)
  (h : c.rel j i) :
  arrow.mk (F.map (X.d_to i)) ≅ arrow.mk (((F.map_homological_complex c).obj X).d_to i) :=
arrow.iso_mk (F.map_iso (homological_complex.X_prev_iso X h) ≪≫
  (eq_to_iso (by refl)) ≪≫ (homological_complex.X_prev_iso _ h).symm) (iso.refl _)
begin
  dsimp,
  simp only [category.id_comp, category.assoc, homological_complex.X_prev_iso_comp_d_to,
  map_homological_complex_obj_d, category.comp_id, X.d_to_eq h, F.map_comp],
end

@[simp]
def map_d_to {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i : M) :
  arrow.mk (F.map (homological_complex.d_to X i)) ≅
    arrow.mk (((F.map_homological_complex c).obj X).d_to i) :=
begin
  rcases h : c.prev i with _ | ⟨j, hij⟩,
  { exact map_d_to₁ F X i h, },
  { exact map_d_to₂ F X i j hij, },
end

lemma map_d_to_eq₁ {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i : M)
  (h : c.prev i = none) :
  map_d_to F X i = map_d_to₁ F X i h :=
by { dsimp, simp only [h], }

lemma map_d_to_eq₂ {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i j : M)
  (h : c.rel j i) :
  map_d_to F X i = map_d_to₂ F X i j h :=
by { dsimp, simp only [c.prev_eq_some h], }

def map_d_from₁ {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i : M)
  (h : c.next i = none) : arrow.mk (F.map (homological_complex.d_from X i)) ≅
    arrow.mk (((F.map_homological_complex c).obj X).d_from i) :=
arrow.iso_mk (iso.refl _) (F.map_iso (homological_complex.X_next_iso_zero X h) ≪≫
  map_zero_object F ≪≫ (homological_complex.X_next_iso_zero _ h).symm)
begin
  dsimp,
  simp only [category.id_comp, zero_comp, comp_zero, homological_complex.d_from_eq_zero _ h],
end

def map_d_from₂ {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i j : M)
  (h : c.rel i j) : arrow.mk (F.map (homological_complex.d_from X i)) ≅
    arrow.mk (((F.map_homological_complex c).obj X).d_from i) :=
arrow.iso_mk (iso.refl _) (F.map_iso (homological_complex.X_next_iso X h) ≪≫
  (eq_to_iso (by refl)) ≪≫ (homological_complex.X_next_iso _ h).symm)
begin
  dsimp,
  simp only [category.id_comp, homological_complex.d_from_eq _ h, ← F.map_comp_assoc,
    map_homological_complex_obj_d, category.assoc, iso.inv_hom_id, category.comp_id],
end

@[simp]
def map_d_from {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i : M) :
  arrow.mk (F.map (homological_complex.d_from X i)) ≅
    arrow.mk (((F.map_homological_complex c).obj X).d_from i) :=
begin
  rcases h : c.next i with _ | ⟨j, hij⟩,
  { exact map_d_from₁ F X i h, },
  { exact map_d_from₂ F X i j hij, },
end

lemma map_d_from_eq₁ {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i : M)
  (h : c.next i = none) :
  map_d_from F X i = map_d_from₁ F X i h :=
by { dsimp, simp only [h], }

lemma map_d_from_eq₂ {M : Type*} {c : complex_shape M} (X : homological_complex C c) (i j : M)
  (h : c.rel i j) :
  map_d_from F X i = map_d_from₂ F X i j h :=
by { dsimp, simp only [c.next_eq_some h], }

end preadditive

end functor

end category_theory
