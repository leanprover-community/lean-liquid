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
include h w

def mono_lift : T ⟶ A :=
(abelian.is_limit_of_exact_of_mono f g h).lift (kernel_fork.of_ι _ w)

@[simp, reassoc] lemma mono_lift_comp : h.mono_lift φ w ≫ f = φ :=
(abelian.is_limit_of_exact_of_mono f g h).fac (kernel_fork.of_ι _ w) walking_parallel_pair.zero

lemma mono_lift_unique (e : T ⟶ A) (he : e ≫ f = φ) : e = h.mono_lift φ w :=
by rw [← cancel_mono f, he, h.mono_lift_comp]

end lift

section desc

variables (h : exact f g) [category_theory.epi g] (φ : B ⟶ T) (w : f ≫ φ = 0)
include h w

def epi_desc : C ⟶ T :=
(abelian.is_colimit_of_exact_of_epi f g h).desc (cokernel_cofork.of_π _ w)

@[simp, reassoc] lemma comp_epi_desc : g ≫ h.epi_desc φ w = φ :=
(abelian.is_colimit_of_exact_of_epi f g h).fac (cokernel_cofork.of_π _ w) walking_parallel_pair.one

lemma epi_desc_unique (e : C ⟶ T) (he : g ≫ e = φ) : e = h.epi_desc φ w :=
by rw [← cancel_epi g, he, h.comp_epi_desc]

end desc

end exact
end category_theory
