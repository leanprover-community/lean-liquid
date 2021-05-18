import polyhedral_lattice.basic
import normed_group.pseudo_normed_group
import pseudo_normed_group.profinitely_filtered

import for_mathlib.coe_nat_abs

noncomputable theory
open_locale nnreal big_operators

namespace polyhedral_lattice

open pseudo_normed_group normed_group

variables (Λ : Type*) [polyhedral_lattice Λ]

lemma filtration_finite (ε : ℝ≥0) : (filtration Λ ε).finite :=
begin
  classical,
  obtain ⟨ι, _ι_inst, l, hl, hl'⟩ := polyhedral_lattice.polyhedral Λ, resetI,
  let n : ι → ℕ := λ i, ⌈(ε / nnnorm (l i) : ℝ)⌉.nat_abs + 1,
  let S := finset.univ.pi (λ i, finset.range (n i)),
  let S' : finset Λ := S.image (λ x, ∑ i, x i (finset.mem_univ _) • l i),
  apply S'.finite_to_set.subset,
  intros l₀ H,
  obtain ⟨c, h1, h2⟩ := hl.generates_nnnorm l₀,
  simp only [S', set.mem_image, finset.mem_univ, finset.mem_pi, forall_true_left, finset.mem_range,
    finset.mem_coe, finset.coe_image],
  refine ⟨λ i _, c i, _, h1.symm⟩,
  rintro i -,
  rw finset.mem_range,
  apply nat.succ_le_succ,
  contrapose! H,
  simp only [not_le, semi_normed_group.mem_filtration_iff, h2],
  have aux : 0 < nnnorm (l i),
  { rw [zero_lt_iff, ne.def, nnnorm_eq_zero], exact hl' i },
  calc ε
      ≤ (⌈(ε / nnnorm (l i) : ℝ)⌉.nat_abs : ℝ≥0) * nnnorm (l i) : _
  ... < ↑(c i) * nnnorm (l i) : _
  ... ≤ ∑ (i : ι), ↑(c i) * nnnorm (l i) : _,
  { rw [← nnreal.div_le_iff aux.ne', ← nnreal.coe_le_coe],
    simp only [coe_nnnorm, nnreal.coe_nat_abs, nnreal.coe_div],
    refine (le_ceil _).trans (le_abs_self _), },
  { rw mul_lt_mul_right aux,
    { exact_mod_cast H }, },
  { refine @finset.single_le_sum _ _ _ _ _ _ i (finset.mem_univ _),
    exact λ _ _, zero_le', }
end

open metric semi_normed_group

instance : discrete_topology Λ :=
discrete_topology_of_open_singleton_zero $
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
      simp only [set.finite.mem_to_finset, mem_filtration_iff] at has₀,
      rwa [← ha] },
    suffices : ({0} : set Λ) = ball (0:Λ) ε,
    { rw this, apply is_open_ball },
    ext,
    simp only [metric.mem_ball, set.mem_singleton_iff, dist_zero_right],
    split,
    { rintro rfl, rw norm_zero, exact_mod_cast h0ε },
    intro h,
    have hx : x ∈ s,
    { simp only [set.finite.mem_to_finset, mem_filtration_iff],
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

-- we don't need this
instance : profinitely_filtered_pseudo_normed_group Λ :=
{ compact := λ c, by apply_instance, -- compact of finite
  continuous_add' := λ _ _, continuous_of_discrete_topology,
  continuous_neg' := λ _, continuous_of_discrete_topology,
  continuous_cast_le := λ _ _ _, continuous_of_discrete_topology,
  .. (show pseudo_normed_group Λ, by apply_instance) }

end polyhedral_lattice
