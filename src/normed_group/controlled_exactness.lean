import for_mathlib.normed_group_hom_completion
import for_mathlib.normed_group_hom
import for_mathlib.specific_limit
/-!

# A controlled exactness lemma for seminormed groups

This file contains a proof of Proposition 8.17 of `analytic.pdf`,
a technical lemma which controls, in some cases, the norm of the map
induced on completions by a normed group hom.

-/
noncomputable theory

open filter set function normed_group uniform_space normed_group_hom finset
open_locale topological_space big_operators

lemma controlled_exactness {M M₁ M₂ : Type*} [semi_normed_group M] [semi_normed_group M₁]
  [semi_normed_group M₂]
  {f : normed_group_hom M₁ M} {C : ℝ} (hC : 0 < C) {D : ℝ}
  {g : normed_group_hom M M₂}
  (h : ∀ m ∈ g.ker, ∃ m' : M₁, f m' = m ∧ ∥m'∥ ≤ C*∥m∥)
  (h' : ∀ x ∈ g.range, ∃ y, g y = x ∧ ∥y∥ ≤ D * ∥x∥) :
  ∀ m ∈ g.completion.ker, ∀ ε > 0, ∃ m' : completion M₁, f.completion m' = m ∧ ∥m'∥ ≤ (C + ε)*∥m∥ :=
begin
  intros hatm hatm_in ε ε_pos,
  by_cases H : hatm = 0,
  { use 0,
    simp [H] },
  set hatf := f.completion,
  set i := incl g.ker,

  have norm_j_comp_i : ∀ x, ∥j.comp i x∥ = ∥x∥,
  { intro x,
    erw [norm_to_compl, norm_incl] },

  have hatm_in : hatm ∈ closure ((j.comp i).range : set $ completion M),
    by rwa ← normed_group_hom.ker_completion h',

  have : ∀ k : g.ker, ∃ m' : completion M₁, hatf m' = (j.comp i) k ∧ ∥m'∥ ≤ C * ∥k∥,
  { rintros ⟨k, k_in⟩,
    rcases h k k_in with ⟨m₁, hm₁, hm₁'⟩,
    use j m₁,
    erw [f.completion_coe, hm₁, norm_to_compl],
    exact ⟨rfl, hm₁'⟩ },
  exact controlled_closure_range_of_complete norm_j_comp_i hC ε_pos this hatm_in
end
