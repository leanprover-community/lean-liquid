import for_mathlib.short_complex

noncomputable theory

open category_theory category_theory.category category_theory.limits

universes v

namespace short_complex

variables {C : Type*} [category C] [has_zero_morphisms C]

@[simps]
def π₁ : short_complex C ⥤ C :=
{ obj := λ S, S.1.X,
  map := λ S₁ S₂ f, f.τ₁, }

@[simps]
def π₂ : short_complex C ⥤ C :=
{ obj := λ S, S.1.Y,
  map := λ S₁ S₂ f, f.τ₂, }

@[simps]
def π₃ : short_complex C ⥤ C :=
{ obj := λ S, S.1.Z,
  map := λ S₁ S₂ f, f.τ₃, }

@[simps]
def φ₁₂ : (π₁ : short_complex C ⥤ C) ⟶ π₂ :=
{ app := λ S, S.1.f,
  naturality' := λ S₁ S₂ f, (composable_morphisms.hom.comm₁₂ f).symm, }

@[simps]
def φ₂₃ : (π₂ : short_complex C ⥤ C) ⟶ π₃ :=
{ app := λ S, S.1.g,
  naturality' := λ S₁ S₂ f, (composable_morphisms.hom.comm₂₃ f).symm, }

end short_complex
