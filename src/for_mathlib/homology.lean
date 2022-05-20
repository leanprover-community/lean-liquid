import algebra.homology.homology
import category_theory.limits.shapes.zero_objects
import category_theory.abelian.homology

import for_mathlib.homology_exact

noncomputable theory

open category_theory category_theory.limits

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]

section
-- jmc: I haven't thought about which of these two is easier to prove
-- they are equivalent using `exact.homology_is_zero` and `exact_of_homology_is_zero`

-- SELFCONTAINED
lemma exact_iff_image_to_kernel'_is_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  exact f g ↔ is_iso (image_to_kernel' f g w) :=
sorry

-- SELFCONTAINED
lemma homology_is_zero_iff_image_to_kernel'_is_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  is_zero (homology f g w) ↔ is_iso (image_to_kernel' f g w) :=
sorry

end
