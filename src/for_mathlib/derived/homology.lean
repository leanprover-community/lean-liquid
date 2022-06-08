import category_theory.limits.preserves.filtered
import for_mathlib.derived.ext_coproducts

noncomputable theory

universes v u

open category_theory category_theory.limits

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐]

section homological_complex

-- requires AB5 condition on `𝓐`
instance chain_complex_homology_preserves_filtered_colimits (i : ℕ) :
  preserves_filtered_colimits $
    @homology_functor ℕ 𝓐 _ _ (complex_shape.down ℕ) _ _ _ _ _ i :=
sorry

end homological_complex

namespace bounded_homotopy_category

def chain_complex_homology_iso (i : ℕ) :
  chain_complex.to_bounded_homotopy_category ⋙
    forget 𝓐 ⋙
    homotopy_category.homology_functor _ _ (-i:ℤ) ≅
  homology_functor _ _ i :=
sorry

instance chain_complex_homology_preserves_filtered_colimits (i : ℤ) :
  preserves_filtered_colimits $
  chain_complex.to_bounded_homotopy_category ⋙
    forget 𝓐 ⋙
    homotopy_category.homology_functor _ _ i :=
sorry

end bounded_homotopy_category
