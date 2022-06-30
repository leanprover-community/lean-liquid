
import for_mathlib.composable_morphisms
import algebra.homology.additive
import for_mathlib.homological_complex_map_d_to_d_from

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
def map_short_complex [has_zero_morphisms C] [has_zero_morphisms D] (F : C ⥤ D)
  [F.preserves_zero_morphisms] :
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

lemma prev_id (X : homological_complex C c) (i : M) : hom.prev (𝟙 X) i = 𝟙 (X.X_prev i) :=
begin
  rcases h : c.prev i with _ | ⟨j,w⟩,
  { rw homological_complex.prev_eq_zero' _ i h,
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
  { simp only [homological_complex.prev_eq_zero' _ i h, comp_zero], },
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

@[simps]
def hom_mk [has_zero_morphisms C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁ ⟶ Z₁}
  {f₂ : X₂ ⟶ Y₂} {g₂ : Y₂ ⟶ Z₂} {zero₁ : f₁ ≫ g₁ = 0} {zero₂ : f₂ ≫ g₂ = 0}
  (τ₁ : X₁ ⟶ X₂) (τ₂ : Y₁ ⟶ Y₂) (τ₃ : Z₁ ⟶ Z₂) (comm₁₂ : f₁ ≫ τ₂ = τ₁ ≫ f₂)
  (comm₂₃ : g₁ ≫ τ₃ = τ₂ ≫ g₂) :
  mk f₁ g₁ zero₁ ⟶ mk f₂ g₂ zero₂ := ⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₃⟩

@[simps]
def iso_mk [has_zero_morphisms C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁ ⟶ Z₁}
  {f₂ : X₂ ⟶ Y₂} {g₂ : Y₂ ⟶ Z₂} {zero₁ : f₁ ≫ g₁ = 0} {zero₂ : f₂ ≫ g₂ = 0}
  (τ₁ : X₁ ≅ X₂) (τ₂ : Y₁ ≅ Y₂) (τ₃ : Z₁ ≅ Z₂) (comm₁₂ : f₁ ≫ τ₂.hom = τ₁.hom ≫ f₂)
  (comm₂₃ : g₁ ≫ τ₃.hom = τ₂.hom ≫ g₂) :
  mk f₁ g₁ zero₁ ≅ mk f₂ g₂ zero₂ :=
{ hom := hom_mk τ₁.hom τ₂.hom τ₃.hom comm₁₂ comm₂₃,
  inv := begin
    refine hom_mk τ₁.inv τ₂.inv τ₃.inv _ _,
    { simp only [← cancel_mono τ₂.hom, ← cancel_epi τ₁.hom,
        assoc, iso.inv_hom_id, comp_id, iso.hom_inv_id_assoc, comm₁₂], },
    { simp only [← cancel_mono τ₃.hom, ← cancel_epi τ₂.hom,
        assoc, iso.inv_hom_id, comp_id, iso.hom_inv_id_assoc, comm₂₃], },
  end,
  hom_inv_id' := begin
    ext,
    { simpa only [comp_τ₁, hom_mk_τ₁, iso.hom_inv_id], },
    { simpa only [comp_τ₂, hom_mk_τ₂, iso.hom_inv_id], },
    { simpa only [comp_τ₃, hom_mk_τ₃, iso.hom_inv_id], },
  end,
  inv_hom_id' := begin
    ext,
    { simpa only [iso.inv_hom_id, comp_τ₁, hom_mk_τ₁], },
    { simpa only [iso.inv_hom_id, comp_τ₂, hom_mk_τ₂], },
    { simpa only [iso.inv_hom_id, comp_τ₃, hom_mk_τ₃], },
  end, }

def homology [abelian C] (S : short_complex C) : C := homology S.1.f S.1.g S.2

@[simps]
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
  map := λ X Y f, composable_morphisms.hom.mk (f.prev i) (f.f i) (f.next i)
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

@[simps]
def homology_functor_iso [abelian C] {M : Type*} (c : complex_shape M) (i : M) :
  _root_.homology_functor C c i ≅
  functor_homological_complex C c i ⋙ short_complex.homology_functor :=
nat_iso.of_components (λ X, iso.refl _)
  (λ X Y f, by { ext, simpa only [iso.refl_hom, id_comp, comp_id], })

variable {C}

def functor_homological_complex_map [preadditive C] [has_zero_object C]
  [preadditive D] [has_zero_object D] (F : C ⥤ D) [F.additive]
  {M : Type*} (c : complex_shape M) (i : M) :
short_complex.functor_homological_complex C c i ⋙ F.map_short_complex ≅
F.map_homological_complex c ⋙ short_complex.functor_homological_complex D c i :=
nat_iso.of_components
  (λ X, iso_mk (F.obj_X_prev X i) (iso.refl _) ((F.obj_X_next X i))
    (by simpa only [iso.refl_hom, comp_id] using F.map_d_to X i)
    (by simpa only [iso.refl_hom, id_comp] using F.d_from_map X i))
  (λ X Y f, begin
    ext,
    { simp only [functor.comp_map, iso_mk_hom, comp_τ₁, functor.map_short_complex_map_τ₁,
        functor_homological_complex_map_τ₁, hom_mk_τ₁, F.map_prev], },
    { dsimp, simp only [comp_id, id_comp], },
    { simp only [functor.comp_map, iso_mk_hom, comp_τ₃, functor.map_short_complex_map_τ₃,
        functor_homological_complex_map_τ₃, hom_mk_τ₃, F.map_next], },
  end)

end short_complex
