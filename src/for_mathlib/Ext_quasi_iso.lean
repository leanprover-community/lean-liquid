import for_mathlib.derived.les_facts


noncomputable theory

universes v u

open category_theory category_theory.limits

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

