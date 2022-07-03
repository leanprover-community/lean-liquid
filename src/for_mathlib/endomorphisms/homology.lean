import for_mathlib.endomorphisms.basic
import algebra.homology.homology


namespace category_theory

namespace endomorphisms

open homological_complex

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [abelian (endomorphisms 𝓐)]
variables {M : Type*} {c : complex_shape M} (F : endomorphisms 𝓐 ⥤ homological_complex 𝓐 c)
variables (Y : homological_complex (endomorphisms 𝓐) c)

@[simps]
def _root_.homological_complex.tautological_endomorphism : Y ⟶ Y :=
{ f := λ i, ⟨(Y.X i).e, rfl⟩, }

lemma homology_functor_obj_e (i : M) :
  ((homology_functor (endomorphisms 𝓐) c i).obj Y).e =
    ((homology_functor (endomorphisms 𝓐) c i).map Y.tautological_endomorphism).f  :=
begin
  sorry
end

end endomorphisms

end category_theory
