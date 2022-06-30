
import for_mathlib.composable_morphisms
import algebra.homology.homological_complex

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C D : Type*} [category C] [category D]

section

variables (C)

/- Category of complexes `X ⟶ Y ⟶ Z` -/
@[derive category]
def short_complex [has_zero_morphisms C] := { S : composable_morphisms C // S.zero }

variables {C}

namespace category_theory

namespace functor

@[simps]
def map_short_complex [has_zero_morphisms C] [has_zero_morphisms D] (F : C ⥤ D) [F.preserves_zero_morphisms] :
  short_complex C ⥤ short_complex D :=
full_subcategory.lift _ (induced_functor _ ⋙ F.map_composable_morphisms)
(λ X, begin
  have h := X.2,
  dsimp [composable_morphisms.zero] at h ⊢,
  rw [← F.map_comp, h, F.map_zero],
end)

end functor

namespace arrow

namespace hom

lemma congr_left {f g : arrow C} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.left = φ₂.left := by rw h
lemma congr_right {f g : arrow C} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.right = φ₂.right := by rw h

end hom

end arrow

end category_theory

end

open category_theory

namespace homological_complex

variables [has_zero_morphisms C] [has_zero_object C] {M : Type*} {c : complex_shape M}

/- there is already `prev_eq_zero` in `les_homology.lean`, but with extra assumptions -/
lemma prev_eq_zero' {X Y : homological_complex C c} (f : X ⟶ Y) (i : M) (h : c.prev i = none) :
  f.prev i = 0 :=
by { dsimp [hom.prev], simpa only [h], }

lemma prev_id (X : homological_complex C c) (i : M) : hom.prev (𝟙 X) i = 𝟙 (X.X_prev i) :=
begin
  rcases h : c.prev i with _ | ⟨j,w⟩,
  { rw prev_eq_zero' _ i h,
    symmetry,
    rw ← limits.is_zero.iff_id_eq_zero,
    exact limits.is_zero.of_iso (limits.is_zero_zero _)
      (homological_complex.X_prev_iso_zero X h), },
  { rw homological_complex.hom.prev_eq _ w,
    simp only [homological_complex.hom.prev_eq _ w,
      homological_complex.id_f, id_comp, iso.hom_inv_id], },
end

lemma next_id (X : homological_complex C c) (i : M) : hom.next (𝟙 X) i = 𝟙 (X.X_next i) :=
arrow.hom.congr_right (hom.sq_from_id X i)

lemma prev_comp {X Y Z : homological_complex C c} (f : X ⟶ Y) (g : Y ⟶ Z)
  (i : M) : hom.prev (f ≫ g) i = hom.prev f i ≫ hom.prev g i :=
begin
  rcases h : c.prev i with _ | ⟨j,w⟩,
  { simp only [prev_eq_zero' _ i h, comp_zero], },
  { simp only [homological_complex.hom.prev_eq _ w, comp_f, assoc, iso.inv_hom_id_assoc], },
end

lemma next_comp {X Y Z : homological_complex C c} (f : X ⟶ Y) (g : Y ⟶ Z)
  (i : M) : hom.next (f ≫ g) i = hom.next f i ≫ hom.next g i :=
arrow.hom.congr_right (hom.sq_from_comp f g i)

end homological_complex

namespace short_complex

@[simps]
def mk [has_zero_morphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (zero : f ≫ g = 0) :
  short_complex C := ⟨composable_morphisms.mk f g, zero⟩

@[simp]
lemma mk_id_τ₁ [has_zero_morphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (zero : f ≫ g = 0) :
composable_morphisms.hom.τ₁ (𝟙 (mk f g zero)) = 𝟙 X := rfl
@[simp]
lemma mk_id_τ₂ [has_zero_morphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (zero : f ≫ g = 0) :
composable_morphisms.hom.τ₂ (𝟙 (mk f g zero)) = 𝟙 Y := rfl
@[simp]
lemma mk_id_τ₃ [has_zero_morphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (zero : f ≫ g = 0) :
composable_morphisms.hom.τ₃ (𝟙 (mk f g zero)) = 𝟙 Z := rfl

@[simp]
lemma comp_τ₁ [has_zero_morphisms C] {S₁ S₂ S₃ : short_complex C} (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
  (f ≫ g).τ₁ = f.τ₁ ≫ g.τ₁ := rfl
@[simp]
lemma comp_τ₂ [has_zero_morphisms C] {S₁ S₂ S₃ : short_complex C} (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
  (f ≫ g).τ₂ = f.τ₂ ≫ g.τ₂ := rfl
@[simp]
lemma comp_τ₃ [has_zero_morphisms C] {S₁ S₂ S₃ : short_complex C} (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
  (f ≫ g).τ₃ = f.τ₃ ≫ g.τ₃ := rfl

def homology [abelian C] (S : short_complex C) : C := homology S.1.f S.1.g S.2

def homology_functor [abelian C] : short_complex C ⥤ C :=
{ obj := λ X, X.homology,
  map := λ X Y φ, homology.map X.2 Y.2 ⟨φ.τ₁, φ.τ₂, φ.comm₁₂.symm⟩
    ⟨φ.τ₂, φ.τ₃, φ.comm₂₃.symm⟩ rfl,
  map_id' := λ X, by apply homology.map_id,
  map_comp' := λ X Y Z φ ψ, by { symmetry, apply homology.map_comp, }, }

variable (C)

@[simps]
def functor_homological_complex [has_zero_morphisms C] [has_zero_object C]
  {M : Type*} (c : complex_shape M) (i : M) :
  homological_complex C c ⥤ short_complex C :=
{ obj := λ X, mk (X.d_to i) (X.d_from i) (X.d_to_comp_d_from i),
  map := λ X Y f, composable_morphisms.hom.mk  (f.prev i) (f.f i) (f.next i)
    (f.comm_to i).symm (f.comm_from i).symm,
  map_id' := λ X, begin
    ext,
    { exact X.prev_id i, },
    { refl, },
    { exact X.next_id i, },
  end,
  map_comp' := λ X Y Z f g, begin
    ext,
    { exact homological_complex.prev_comp f g i, },
    { refl, },
    { exact homological_complex.next_comp f g i, },
  end, }

end short_complex
