
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
def short_complex [has_zero_morphisms C] := full_subcategory $ λ S : composable_morphisms C, S.zero

end

open category_theory

namespace homological_complex

variables [has_zero_morphisms C] {M : Type*} {c : complex_shape M}

lemma prev_id (X : homological_complex C c) (i : M) : hom.prev (𝟙 X) i = 𝟙 (X.X_prev i) := rfl

lemma next_id (X : homological_complex C c) (i : M) : hom.next (𝟙 X) i = 𝟙 (X.X_next i) := rfl

lemma prev_comp {X Y Z : homological_complex C c} (f : X ⟶ Y) (g : Y ⟶ Z)
  (i : M) : hom.prev (f ≫ g) i = hom.prev f i ≫ hom.prev g i := rfl

lemma next_comp {X Y Z : homological_complex C c} (f : X ⟶ Y) (g : Y ⟶ Z)
  (i : M) : hom.next (f ≫ g) i = hom.next f i ≫ hom.next g i := rfl

end homological_complex

namespace short_complex

@[simp, reassoc]
lemma zero [has_zero_morphisms C] (S : short_complex C) : S.1.f ≫ S.1.g = 0 := S.2

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
def iso_mk [has_zero_morphisms C] {S₁ S₂ : short_complex C}
  (τ₁ : S₁.1.X ≅ S₂.1.X) (τ₂ : S₁.1.Y ≅ S₂.1.Y) (τ₃ : S₁.1.Z ≅ S₂.1.Z)
  (comm₁₂ : S₁.1.f ≫ τ₂.hom = τ₁.hom ≫ S₂.1.f)
  (comm₂₃ : S₁.1.g ≫ τ₃.hom = τ₂.hom ≫ S₂.1.g) :
  S₁ ≅ S₂ :=
{ hom := ⟨τ₁.hom, τ₂.hom, τ₃.hom, comm₁₂, comm₂₃⟩,
  inv := begin
    refine ⟨τ₁.inv, τ₂.inv, τ₃.inv, _, _⟩,
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

lemma is_iso_of_is_isos [has_zero_morphisms C] {S₁ S₂ : short_complex C}
  (φ : S₁ ⟶ S₂) (h₁ : is_iso φ.τ₁) (h₂ : is_iso φ.τ₂) (h₃ : is_iso φ.τ₃) : is_iso φ :=
begin
  let e : S₁ ≅ S₂ := iso_mk (as_iso φ.τ₁) (as_iso φ.τ₂) (as_iso φ.τ₃) φ.comm₁₂ φ.comm₂₃,
  unfreezingI { rcases φ with ⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₂⟩, },
  exact is_iso.of_iso e,
end

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
def functor_homological_complex [has_zero_morphisms C]
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

end short_complex

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

namespace nat_trans

@[simps]
def map_short_complex [has_zero_morphisms C] [has_zero_morphisms D] {F G : C ⥤ D}
  [F.preserves_zero_morphisms] [G.preserves_zero_morphisms] (φ : F ⟶ G) :
  F.map_short_complex ⟶ G.map_short_complex :=
{ app := λ X, ⟨φ.app _, φ.app _, φ.app _, φ.naturality _, φ.naturality _⟩, }

end nat_trans

end category_theory

open category_theory

namespace short_complex

variable {C}

def functor_homological_complex_map [preadditive C] [preadditive D] (F : C ⥤ D) [F.additive]
  {M : Type*} (c : complex_shape M) (i : M) :
short_complex.functor_homological_complex C c i ⋙ F.map_short_complex ≅
F.map_homological_complex c ⋙ short_complex.functor_homological_complex D c i :=
iso.refl _

variables [preadditive C] [preadditive D] {F G : C ⥤ D} [functor.additive F] [functor.additive G]
  {M : Type*} (c : complex_shape M) (i : M) (φ : F ⟶ G) (X : homological_complex C c)

lemma nat_trans.map_short_complex_app :
  (nat_trans.map_short_complex φ).app ((short_complex.functor_homological_complex C c i).obj X) =
  (short_complex.functor_homological_complex D c i).map
    ((nat_trans.map_homological_complex φ c).app X) := rfl

lemma naturality_functor_homological_complex_map :
  (nat_trans.map_short_complex φ).app
    ((short_complex.functor_homological_complex C c i).obj X) ≫
    (short_complex.functor_homological_complex_map G c i).hom.app X =
  (short_complex.functor_homological_complex_map F c i).hom.app X ≫
    (short_complex.functor_homological_complex D c i).map
      ((nat_trans.map_homological_complex φ c).app X) :=
begin
  dsimp only [functor_homological_complex_map, iso.refl_hom, nat_trans.id_app],
  erw [nat_trans.map_short_complex_app, category.id_comp, category.comp_id],
end

end short_complex
