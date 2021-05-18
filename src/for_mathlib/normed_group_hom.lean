import analysis.normed_space.normed_group_hom
import topology.algebra.normed_group

import for_mathlib.normed_group

noncomputable theory

open set normed_group_hom uniform_space

variables {G : Type*} [semi_normed_group G]
variables {H : Type*} [semi_normed_group H]

lemma controlled_closure_of_complete [complete_space G] {f : normed_group_hom G H} {K : add_subgroup H}
  {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) (hyp : ∀ h ∈ K, ∃ g, f g = h ∧ ∥g∥ ≤ C*∥h∥) :
  ∀ {h}, h ∈ K.topological_closure → ∃ g, f g = h ∧ ∥g∥ ≤ (C + ε)*∥h∥ :=
begin
  intros h h_in,
  by_cases hyp_h : h = 0,
  { rw hyp_h,
    use 0,
    simp },
  sorry
end

lemma controlled_closure_range_of_complete [complete_space G] {f : normed_group_hom G H}
  {K : Type*} [semi_normed_group K] {j : normed_group_hom K H} (hj : ∀ x, ∥j x∥ = ∥x∥)
  {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) (hyp : ∀ k, ∃ g, f g = j k ∧ ∥g∥ ≤ C*∥k∥) :
  ∀ {h}, h ∈ j.range.topological_closure → ∃ g, f g = h ∧ ∥g∥ ≤ (C + ε)*∥h∥ :=
begin
  replace hyp : ∀ h ∈ j.range, ∃ g, f g = h ∧ ∥g∥ ≤ C*∥h∥,
  { intros h h_in,
    rcases (j.mem_range _).mp h_in with ⟨k, rfl⟩,
    rw hj,
    exact hyp k },
  exact λ _, controlled_closure_of_complete hC hε hyp
end
