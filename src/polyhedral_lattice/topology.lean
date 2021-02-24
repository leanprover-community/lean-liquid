import polyhedral_lattice.basic
import normed_group.pseudo_normed_group
import pseudo_normed_group.profinitely_filtered 

import for_mathlib.topological_group
import for_mathlib.topology

noncomputable theory
open_locale nnreal

namespace polyhedral_lattice

open pseudo_normed_group normed_group

variables (Λ : Type*)
variables [normed_group Λ] [polyhedral_lattice Λ]

lemma filtration_finite (c : ℝ≥0) : (filtration Λ c).finite :=
begin
  sorry
end

open metric

instance : discrete_topology Λ :=
discrete_topology_of_open_singleton_zero _ $
begin
  classical,
  have aux := filtration_finite Λ 1,
  let s := aux.to_finset,
  let s₀ := s.erase 0,
  by_cases hs₀ : s₀.nonempty,
  { let ε : ℝ≥0 := finset.min' (s₀.image $ nnnorm) (hs₀.image _),
    obtain ⟨a, has₀, ha⟩ : ∃ a ∈ s₀, nnnorm a = ε,
    { rw ← finset.mem_image, apply finset.min'_mem },
    have H : 0 < ∥a∥ := by simpa only [norm_pos_iff] using finset.ne_of_mem_erase has₀,
    have h0ε : 0 < ε, { simpa only [← ha] },
    have hε1 : ε ≤ 1,
    { replace has₀ := finset.mem_of_mem_erase has₀,
      simp only [set.finite.mem_to_finset, mem_filtration_iff, nnreal.coe_one] at has₀,
      rwa [← ha] },
    suffices : ({0} : set Λ) = ball (0:Λ) ε,
    { rw this, apply is_open_ball },
    ext,
    simp only [metric.mem_ball, set.mem_singleton_iff, dist_zero_right],
    split,
    { rintro rfl, rw norm_zero, exact_mod_cast h0ε },
    intro h,
    have hx : x ∈ s,
    { simp only [set.finite.mem_to_finset, mem_filtration_iff, nnreal.coe_one],
      exact le_of_lt (lt_of_lt_of_le h hε1) },
    by_contra hx0,
    replace hx := finset.mem_erase_of_ne_of_mem hx0 hx,
    have := finset.min'_le (s₀.image $ nnnorm),
    refine not_lt.2 (this (nnnorm x) _) h,
    simp only [exists_prop, set.finite.mem_to_finset, finset.mem_image],
    use ⟨x, ⟨hx, rfl⟩⟩ },
  { suffices : ({0} : set Λ) = ball (0:Λ) 1,
    { rw this, apply is_open_ball },
    ext,
    simp only [metric.mem_ball, set.mem_singleton_iff, dist_zero_right],
    split,
    { rintro rfl, rw norm_zero, exact zero_lt_one },
    intro h,
    contrapose! hs₀,
    refine ⟨x, _⟩,
    simp only [set.finite.mem_to_finset, finset.mem_erase, mem_filtration_iff, nnreal.coe_one],
    exact ⟨hs₀, h.le⟩ }
end

instance filtration_fintype (c : ℝ≥0) : fintype (filtration Λ c) :=
(filtration_finite Λ c).fintype

instance : profinitely_filtered_pseudo_normed_group Λ :=
{ compact := λ c, by apply_instance, -- compact of finite
  continuous_add' := λ _ _, continuous_of_discrete_topology,
  continuous_neg' := λ _, continuous_of_discrete_topology,
  continuous_cast_le := λ _ _ _, continuous_of_discrete_topology,
  .. (show pseudo_normed_group Λ, by apply_instance) }

end polyhedral_lattice
