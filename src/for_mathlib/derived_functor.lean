import category_theory.derived
import data.matrix.notation

import for_mathlib.homological_complex
import for_mathlib.horseshoe
import for_mathlib.split_exact

noncomputable theory

open category_theory
open category_theory.limits
open short_exact_sequence

universes v u

namespace category_theory

variables {C : Type u} [category.{v} C] {D : Type*} [category D]

-- Importing `category_theory.abelian.projective` and assuming
-- `[abelian C] [enough_projectives C] [abelian D]` suffices to acquire all the following:
-- variables [preadditive C] [has_zero_object C] [has_equalizers C]
-- variables [has_images C] [has_projective_resolutions C]
-- variables [preadditive D] [has_zero_object D] [has_equalizers D] [has_cokernels D]
-- variables [has_images D] [has_image_maps D]

variables [abelian C] [enough_projectives C] [abelian D]

namespace functor
namespace left_derived

variables (F : C ⥤ D)

/-- We can compute a left derived functor using a chosen projective resolution. -/
@[simps]
def functor.left_derived_obj_iso' (F : C ⥤ D) [F.additive] (n : ℕ)
  (X : C) (P : chain_complex C ℕ) (π : P ⟶ ((chain_complex.single₀ C).obj X))
  (h : P.is_projective_resolution X π) :
  (F.left_derived n).obj X ≅
    (homology_functor D _ n).obj ((F.map_homological_complex _).obj P) :=
(F.left_derived_obj_iso n (h.mk_ProjectiveResolution P X π) : _)
.

def δ [F.additive] (n : ℕ) (A : short_exact_sequence C) :
  (F.left_derived (n+1)).obj A.3 ⟶ (F.left_derived n).obj A.1 :=
sorry -- use `for_mathlib/homological_complex.lean`

lemma six_term_exact_seq [F.additive] (n : ℕ) (A : short_exact_sequence C) :
  exact_seq D [
    (F.left_derived (n+1)).map A.f, (F.left_derived (n+1)).map A.g,
    δ F n A,
    (F.left_derived n).map A.f, (F.left_derived n).map A.g] := sorry

end left_derived
end functor
end category_theory
