import for_mathlib.snake_lemma2
import for_mathlib.homology
import for_mathlib.exact_seq2

noncomputable theory

open category_theory category_theory.limits

variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]
variables (A₁ B₁ C₁ : 𝒜)
variables (A₂ B₂ C₂ : 𝒜)
variables (A₃ B₃ C₃ : 𝒜)
variables (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁)
variables (a₁ : A₁ ⟶ A₂) (b₁ : B₁ ⟶ B₂) (c₁ : C₁ ⟶ C₂)
variables (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)
variables (a₂ : A₂ ⟶ A₃) (b₂ : B₂ ⟶ B₃) (c₂ : C₂ ⟶ C₃)
variables (f₃ : A₃ ⟶ B₃) (g₃ : B₃ ⟶ C₃)

namespace category_theory

local notation `kernel_map`   := kernel.map _ _ _ _
local notation `cokernel_map` := cokernel.map _ _ _ _

namespace snake

lemma mk_of_homology
  (sq₁ : a₁ ≫ f₂ = f₁ ≫ b₁)
  (sq₂ : b₁ ≫ g₂ = g₁ ≫ c₁)
  (sq₃ : a₂ ≫ f₃ = f₂ ≫ b₂)
  (sq₄ : b₂ ≫ g₃ = g₂ ≫ c₂)
  (wa : a₁ ≫ a₂ = 0) (wb : b₁ ≫ b₂ = 0) (wc : c₁ ≫ c₂ = 0)
  [exact f₁ g₁] [exact f₂ g₂] [epi g₁] [mono f₂] : snake
  (kernel a₁) (kernel b₁) (kernel c₁)
  A₁ B₁ C₁
  (kernel a₂) (kernel b₂) (kernel c₂)
  (homology _ _ wa) (homology _ _ wb) (homology _ _ wc)
  (kernel.lift _ (kernel.ι _ ≫ f₁) sorry) (kernel.lift _ (kernel.ι _ ≫ g₁) sorry)
  (kernel.ι _) (kernel.ι _) (kernel.ι _)
  f₁ g₁
  (kernel.lift _ _ wa) (kernel.lift _ _ wb) (kernel.lift _ _ wc)
  (kernel.lift _ (kernel.ι _ ≫ f₂) sorry) (kernel.lift _ (kernel.ι _ ≫ g₂) sorry)
  (homology.π' _ _ _) (homology.π' _ _ _) (homology.π' _ _ _)
  (homology.map _ _ ⟨f₁,f₂,sq₁.symm⟩ ⟨f₂, f₃, sq₃.symm⟩ rfl)
  (homology.map _ _ ⟨g₁,g₂,sq₂.symm⟩ ⟨g₂, g₃, sq₄.symm⟩ rfl) := sorry

end snake

end category_theory
