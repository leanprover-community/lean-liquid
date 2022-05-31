import for_mathlib.truncation
import for_mathlib.derived.les_facts


noncomputable theory

universes v u

open category_theory category_theory.limits

-- move this
namespace bounded_homotopy_category

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]

lemma Ext_map_is_iso_of_quasi_iso
  (A₁ A₂ B : bounded_homotopy_category 𝓐) (f : A₁ ⟶ A₂)
  [homotopy_category.is_quasi_iso f] (i : ℤ) :
  is_iso $ ((Ext i).map f.op).app B :=
begin
  sorry
end

end bounded_homotopy_category

namespace cochain_complex
open bounded_homotopy_category

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
variables (C : cochain_complex 𝓐 ℤ)

lemma Ext_ι_succ_five_term_exact_seq (B : bounded_homotopy_category 𝓐) (i j : ℤ) :
  let E := λ n, ((Ext n).flip.obj B) in
  exact_seq Ab.{v} $
    [ (E j).map (bounded_homotopy_category.of_hom (truncation.ι_succ C i)).op
    , (E j).map (bounded_homotopy_category.of_hom (truncation.to_imker C (i+1))).op
    , Ext_δ _ _ j B (truncation.short_exact_ι_succ_to_imker C i)
    , (E (j+1)).map (bounded_homotopy_category.of_hom (truncation.ι_succ C i)).op ] :=
Ext_five_term_exact_seq' _ _ _ _ $
  truncation.short_exact_ι_succ_to_imker C _

end cochain_complex
