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

-- SELFCONTAINED
def lift (h : exact f g) [mono f] (φ : T ⟶ B) (w : φ ≫ g = 0) : T ⟶ A :=
abelian.mono_lift f φ sorry

@[reassoc] lemma lift_comp : h.lift φ w ≫ f = φ := abelian.mono_lift_comp f φ _

lemma lift_unique (e : T ⟶ A) (he : e ≫ f = φ) : e = h.lift φ w :=
by rw [← cancel_mono f, he, h.lift_comp]

end lift

section desc

variables (h : exact f g) [category_theory.epi g] (φ : B ⟶ T) (w : f ≫ φ = 0)

-- SELFCONTAINED
def desc (h : exact f g) [category_theory.epi g] (φ : B ⟶ T) (w : f ≫ φ = 0) : C ⟶ T :=
abelian.epi_desc g φ sorry

@[reassoc] lemma comp_desc : g ≫ h.desc φ w = φ := abelian.comp_epi_desc g φ _

lemma desc_unique (e : C ⟶ T) (he : g ≫ e = φ) : e = h.desc φ w :=
by rw [← cancel_epi g, he, h.comp_desc]

end desc

end exact
end category_theory
