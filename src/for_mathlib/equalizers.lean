import category_theory.limits.shapes.equalizers

noncomputable theory

namespace category_theory
open category

namespace limits

namespace equalizer

variables {C : Type*} [category C]
variables {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} {f₁ g₁ : X₁ ⟶ Y₁} {f₂ g₂ : X₂ ⟶ Y₂} {f₃ g₃ : X₃ ⟶ Y₃}
variables (φ : X₁ ⟶ X₂) (ψ : Y₁ ⟶ Y₂) (φ' : X₂ ⟶ X₃) (ψ' : Y₂ ⟶ Y₃)

section
variables {φ ψ φ' ψ'}
-- better name, better place?
lemma comm_sq₀ : f₁ ≫ 𝟙 _ = 𝟙 _ ≫ f₁ := by rw [comp_id, id_comp]

lemma comm_sq₂ (hf : f₁ ≫ ψ = φ ≫ f₂) (hf' : f₂ ≫ ψ' = φ' ≫ f₃) :
  f₁ ≫ (ψ ≫ ψ') = (φ ≫ φ') ≫ f₃ :=
by rw [← category.assoc, hf, category.assoc, hf', category.assoc]

end

variables [has_equalizers C]

def map (φ : X₁ ⟶ X₂) (ψ : Y₁ ⟶ Y₂) (hf : f₁ ≫ ψ = φ ≫ f₂) (hg : g₁ ≫ ψ = φ ≫ g₂) :
  equalizer f₁ g₁ ⟶ equalizer f₂ g₂ :=
equalizer.lift (equalizer.ι _ _ ≫ φ) $
by rw [category.assoc, category.assoc, ← hf, ← hg, equalizer.condition_assoc]

@[simp, reassoc] lemma map_ι (hf : f₁ ≫ ψ = φ ≫ f₂) (hg : g₁ ≫ ψ = φ ≫ g₂) :
  map φ ψ hf hg ≫ ι _ _ = ι _ _ ≫ φ :=
lift_ι _ _

@[simp] lemma map_id : @map _ _ _ _ _ _ f₁ g₁ f₁ g₁ _ (𝟙 X₁) (𝟙 Y₁) comm_sq₀ comm_sq₀ = 𝟙 _ :=
by { ext, simp only [map_ι, id_comp, comp_id] }

lemma map_comp_map (hf : f₁ ≫ ψ = φ ≫ f₂) (hg : g₁ ≫ ψ = φ ≫ g₂)
  (hf' : f₂ ≫ ψ' = φ' ≫ f₃) (hg' : g₂ ≫ ψ' = φ' ≫ g₃) :
  map φ ψ hf hg ≫ map φ' ψ' hf' hg' =
    map (φ ≫ φ') (ψ ≫ ψ') (comm_sq₂ hf hf') (comm_sq₂ hg hg') :=
by { ext, simp only [map_ι, map_ι_assoc, category.assoc] }

end equalizer

end limits

end category_theory

#lint- only unused_arguments
