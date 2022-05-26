import for_mathlib.abelian_category
import for_mathlib.exact_seq3

noncomputable theory

open category_theory category_theory.limits

namespace category_theory
namespace exact

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables {A B C T : 𝓐} {f : A ⟶ B} {g : B ⟶ C}

section lift

variables (h : exact f g) [mono f] (φ : T ⟶ B) (w : φ ≫ g = 0)

def mono_lift (h : exact f g) [mono f] (φ : T ⟶ B) (w : φ ≫ g = 0) : T ⟶ A :=
abelian.mono_lift f φ $
  by { obtain ⟨t, rfl⟩ := kernel.lift' _ _ w, simp [kernel_comp_cokernel _ _ h] }

@[reassoc] lemma mono_lift_comp : h.mono_lift φ w ≫ f = φ := abelian.mono_lift_comp f φ _

lemma mono_lift_unique (e : T ⟶ A) (he : e ≫ f = φ) : e = h.mono_lift φ w :=
by rw [← cancel_mono f, he, h.mono_lift_comp]

end lift

section desc

variables (h : exact f g) [category_theory.epi g] (φ : B ⟶ T) (w : f ≫ φ = 0)

def epi_desc (h : exact f g) [category_theory.epi g] (φ : B ⟶ T) (w : f ≫ φ = 0) : C ⟶ T :=
abelian.epi_desc g φ $
  by { obtain ⟨t, rfl⟩ := cokernel.desc' _ _ w, simp [kernel_comp_cokernel_assoc _ _ h] }

@[reassoc] lemma comp_epi_desc : g ≫ h.epi_desc φ w = φ := abelian.comp_epi_desc g φ _

lemma epi_desc_unique (e : C ⟶ T) (he : g ≫ e = φ) : e = h.epi_desc φ w :=
by rw [← cancel_epi g, he, h.comp_epi_desc]

end desc

end exact
end category_theory
