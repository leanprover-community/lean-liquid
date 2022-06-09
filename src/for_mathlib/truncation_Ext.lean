import for_mathlib.truncation
import for_mathlib.Ext_quasi_iso


noncomputable theory

universes v u

open category_theory category_theory.limits

namespace cochain_complex
open bounded_homotopy_category

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
variables (C : cochain_complex 𝓐 ℤ)

lemma Ext_ι_succ_five_term_exact_seq (B : bounded_homotopy_category 𝓐) (i j : ℤ) :
  let E := λ n, ((Ext n).flip.obj B) in
  exact_seq Ab.{v} $
    [
      (E j).map (bounded_homotopy_category.of_hom (truncation.to_imker C (i+1))).op
    , (E j).map (bounded_homotopy_category.of_hom (truncation.ι_succ C i)).op
    , Ext_δ _ _ j B (truncation.short_exact_ι_succ_to_imker C i)
    , (E (j+1)).map (bounded_homotopy_category.of_hom (truncation.to_imker C (i+1))).op ] :=
Ext_five_term_exact_seq' _ _ j B (truncation.short_exact_ι_succ_to_imker C i)

end cochain_complex
