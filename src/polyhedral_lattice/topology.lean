import polyhedral_lattice.basic
import normed_group.pseudo_normed_group
import pseudo_normed_group.profinitely_filtered

noncomputable theory
open_locale nnreal big_operators

namespace polyhedral_lattice

open pseudo_normed_group normed_group

variables (Λ : Type*) [polyhedral_lattice Λ]

lemma filtration_finite (c : ℝ≥0) : (filtration Λ c).finite :=
begin
  classical,
  obtain ⟨ι, _ι_inst, l, hl, hl', hl''⟩ := polyhedral_lattice.polyhedral Λ, resetI,
  let n : ι → ℕ := λ i, ⌈(c / nnnorm (l i) : ℝ)⌉.nat_abs + 1,
  let S := finset.univ.pi (λ i, finset.range (n i)),
  -- the following step is not good enough, because the `l i` need not be a basis
  let S' : finset Λ := S.image (λ x, ∑ i, x i (finset.mem_univ _) • l i),
  apply S'.finite_to_set.subset,
  intros l₀ hl₀,
  simp only [set.mem_image, finset.mem_univ, finset.mem_pi, forall_true_left,
    finset.mem_range, finset.mem_coe, finset.coe_image],
  obtain ⟨d, hd, c, h1, h2⟩ := hl l₀,
  sorry

  -- by_cases hι : nonempty ι, swap,
  -- { suffices : filtration Λ c ⊆ {0}, { exact (set.finite_singleton (0:Λ)).subset this },
  --   intros x hx,
  --   simp only [set.mem_singleton_iff],
  --   obtain ⟨d, hd, c, h1, h2⟩ := hl x,
  --   simpa only [finset.univ_eq_empty.mpr hι, finset.sum_empty, smul_eq_zero, hd.ne', false_or]
  --     using h1 },
  -- { let ε := (finset.univ.image (λ i, nnnorm (l i))).min' _,
  --   swap, { simp only [finset.nonempty.image_iff], obtain ⟨i⟩ := hι, exact ⟨i, finset.mem_univ i⟩ },
  --   sorry
  --    }
end

lemma exists_filtration_finite : ∃ (c : ℝ≥0), 0 < c ∧ (filtration Λ c).finite :=
begin
  obtain ⟨ι, _ι_inst, l, hl⟩ := polyhedral_lattice.polyhedral Λ, resetI,
  sorry
end

open metric semi_normed_group

instance : discrete_topology Λ :=
discrete_topology_of_open_singleton_zero $
begin
  classical,
  obtain ⟨c, hc, aux⟩ := exists_filtration_finite Λ,
  let s := aux.to_finset,
  let s₀ := s.erase 0,
  by_cases hs₀ : s₀.nonempty,
  { let ε : ℝ≥0 := finset.min' (s₀.image $ nnnorm) (hs₀.image _),
    obtain ⟨a, has₀, ha⟩ : ∃ a ∈ s₀, nnnorm a = ε,
    { rw ← finset.mem_image, apply finset.min'_mem },
    have H : 0 < ∥a∥ := by simpa only [norm_pos_iff] using finset.ne_of_mem_erase has₀,
    have h0ε : 0 < ε, { simpa only [← ha] },
    have hεc : ε ≤ c,
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
      exact le_of_lt (lt_of_lt_of_le h hεc) },
    by_contra hx0,
    replace hx := finset.mem_erase_of_ne_of_mem hx0 hx,
    have := finset.min'_le (s₀.image $ nnnorm),
    refine not_lt.2 (this (nnnorm x) _) h,
    simp only [exists_prop, set.finite.mem_to_finset, finset.mem_image],
    use ⟨x, ⟨hx, rfl⟩⟩ },
  { suffices : ({0} : set Λ) = ball (0:Λ) c,
    { rw this, apply is_open_ball },
    ext,
    simp only [metric.mem_ball, set.mem_singleton_iff, dist_zero_right],
    split,
    { rintro rfl, rw norm_zero, exact hc },
    intro h,
    contrapose! hs₀,
    refine ⟨x, _⟩,
    simp only [set.finite.mem_to_finset, finset.mem_erase, mem_filtration_iff, nnreal.coe_one],
    exact ⟨hs₀, h.le⟩ }
end

-- lemma filtration_finite (c : ℝ≥0) : (filtration Λ c).finite :=
-- begin
--   admit
-- end

-- instance filtration_fintype (c : ℝ≥0) : fintype (filtration Λ c) :=
-- (filtration_finite Λ c).fintype

-- instance : profinitely_filtered_pseudo_normed_group Λ :=
-- { compact := λ c, by apply_instance, -- compact of finite
--   continuous_add' := λ _ _, continuous_of_discrete_topology,
--   continuous_neg' := λ _, continuous_of_discrete_topology,
--   continuous_cast_le := λ _ _ _, continuous_of_discrete_topology,
--   .. (show pseudo_normed_group Λ, by apply_instance) }

end polyhedral_lattice
