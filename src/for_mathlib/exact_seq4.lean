import for_mathlib.abelian_category
import for_mathlib.exact_seq3

noncomputable theory

namespace category_theory
open category_theory.limits

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]

-- -- SELFCONTAINED
-- lemma exact_seq.is_iso_of_is_zero_of_is_zero
--   {A B C D : 𝓐} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} {L : list (arrow 𝓐)}
--   (H : exact_seq 𝓐 (f::g::h::L)) (hA : is_zero A) (hD : is_zero D) :
--   is_iso g :=
-- begin
--   admit
-- end

end category_theory
