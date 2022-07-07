import for_mathlib.split_exact

noncomputable theory

universes u
open_locale tensor_product

open category_theory category_theory.limits opposite


lemma preserves_finite_limits_of_preserves_mono_preserves_finite_colimits
  {𝓐 𝓑 : Type*} [category 𝓐] [category 𝓑] [abelian 𝓐] [abelian 𝓑]
  (F : 𝓐 ⥤ 𝓑) (h1 : ∀ ⦃X Y : 𝓐⦄ (f : X ⟶ Y), mono f → mono (F.map f))
  [preserves_finite_colimits F] :
  preserves_finite_limits F :=
sorry
