import polyhedral_lattice.basic
import normed_group.pseudo_normed_group
import pseudo_normed_group.profinitely_filtered

noncomputable theory
open_locale nnreal big_operators

namespace polyhedral_lattice

open pseudo_normed_group normed_group

variables (Λ : Type*) [polyhedral_lattice Λ]

section star

/-!
This section only needs the `finite_free` part of polyhedral lattices
-/

variables {Λ} (s : set Λ)

def star (s : set Λ) : set Λ :=
{l' | ∃ (l : Λ) (m n : ℕ), l ∈ s ∧ 0 < m ∧ m ≤ n ∧ m • l = n • l' }

lemma mem_star_iff (l' : Λ) :
  l' ∈ star s ↔ ∃ (l : Λ) (m n : ℕ), l ∈ s ∧ 0 < m ∧ m ≤ n ∧ m.coprime n ∧ m • l = n • l' :=
begin
  split,
  { rintro ⟨l, m, n, hls, h0m, hmn, H⟩,
    let c := m.gcd n,
    have hc : 0 < c := nat.gcd_pos_of_pos_left _ h0m,
    refine ⟨l, m / c, n / c, hls, _, _, nat.coprime_div_gcd_div_gcd hc, _⟩,
    { exact nat.div_pos (nat.gcd_le_left _ h0m) hc },
    { exact nat.div_le_div_right hmn },
    { apply smul_left_injective Λ hc.ne', dsimp,
      simp only [← mul_nsmul],
      rw [nat.mul_div_cancel', nat.mul_div_cancel', H],
      { exact nat.gcd_dvd_right _ _ },
      { exact nat.gcd_dvd_left _ _ } } },
  { rintro ⟨l, m, n, hls, h0m, hmn, -, H⟩, exact ⟨l, m, n, hls, h0m, hmn, H⟩ }
end

lemma star_mono {s t : set Λ} (h : s ⊆ t) : star s ⊆ star t :=
by { rintro l' ⟨l, m, n, hls, H⟩, exact ⟨l, m, n, h hls, H⟩ }

lemma star_eq_Union_star_singleton :
  star s = ⋃ l ∈ s, star {l} :=
begin
  apply set.subset.antisymm,
  { rintro l' ⟨l, m, n, hls, H⟩,
    simp only [exists_prop, set.mem_Union],
    refine ⟨_, hls, ⟨l, m, n, set.mem_singleton _, H⟩⟩, },
  { simp only [set.Union_subset_iff],
    intros l hl, apply star_mono, exact set.singleton_subset_iff.mpr hl }
end

lemma star_zero : star ({0} : set Λ) = {0} :=
begin
  ext x,
  split,
  { intro h,
    obtain ⟨l, n, m, hl, hn, hm, hcopr, hprod⟩ := (mem_star_iff _ _).1 h,
    rw [set.mem_singleton_iff] at hl ⊢,
    rw [hl, smul_zero] at hprod,
    cases smul_eq_zero.1 hprod.symm with hm0 hx,
    { rw hm0 at hm,
      exfalso,
      exact not_le_of_gt hn hm },
    { exact hx } },
  { intro h,
    refine (mem_star_iff _ _).2 ⟨0, 1, 1, set.mem_singleton 0, zero_lt_one, le_refl 1,
    (nat.coprime_self 1).2 rfl , _⟩,
    rw [set.mem_singleton_iff] at h,
    rw [h] }
end

lemma star_singleton_finite (l : Λ) : (star ({l} : set Λ)).finite :=
begin
  by_cases lzero : l = 0,
  { rw [lzero, star_zero],
    exact set.finite_singleton 0 },
  obtain ⟨ι, hι, ⟨b⟩⟩ := polyhedral_lattice.finite_free Λ, resetI,
  let N := b.repr l,
  let g := (N.support.gcd N).nat_abs,
  let l₀ := b.repr.symm (N.map_range (λ k, k / g) (int.zero_div _)),
  let μ : ℕ → Λ := λ n, n • l₀,
  have hg : 0 < g,
  { refine nat.pos_of_ne_zero (λ h, _),
    replace h := finset.gcd_eq_zero_iff.1 (int.eq_zero_of_nat_abs_eq_zero h),
    have hzero : ∀ (i : ι), (b.coord i) l = 0,
    { intro i,
      by_cases hsupp : i ∈ N.support,
      { exact h i hsupp },
      { exact finsupp.not_mem_support_iff.1 hsupp } },
    exact lzero ((basis.forall_coord_eq_zero_iff b).1 hzero) },
  have hgN : ∀ i, (g : ℤ) ∣ N i,
  { intros i,
    by_cases hi : i ∈ N.support,
    { rw [int.nat_abs_dvd], apply finset.gcd_dvd hi },
    { rw finsupp.not_mem_support_iff at hi, rw hi, exact dvd_zero _ } },
  have hgl₀ : g • l₀ = l,
  { apply b.repr.injective, ext i,
    rw [← gsmul_coe_nat, b.repr.map_smul, finsupp.smul_apply, linear_equiv.apply_symm_apply,
      finsupp.map_range_apply, smul_eq_mul, int.mul_div_cancel'],
    exact hgN i, },
  classical,
  suffices : ((finset.Ico 1 (g+1)).image μ : set Λ) = star {l},
  { rw ← this, exact finset.finite_to_set _ },
  ext l',
  simp only [set.mem_image, finset.mem_coe, finset.coe_image, finset.Ico.mem],
  split,
  { rintro ⟨n, ⟨h1n, hng⟩, H⟩,
    refine ⟨l, n, g, set.mem_singleton _, h1n, _, _⟩,
    { exact nat.le_of_succ_le_succ hng },
    { rw [← hgl₀, ← H, smul_comm], } },
  { rw mem_star_iff,
    rintro ⟨l'', m, n, hll'', h0m, hmn, hmn_cop, H⟩,
    rw set.mem_singleton_iff at hll'', subst l'',
    have h0n : 0 < n := h0m.trans_le hmn,
    have hnmg : n ∣ m * g, { sorry },
    refine ⟨m * g / n, ⟨_, _⟩, _⟩,
    { exact nat.div_pos (nat.le_of_dvd (nat.mul_pos h0m hg) hnmg) h0n },
    { rw [nat.div_lt_iff_lt_mul _ _ h0n, mul_comm],
      calc g * m
          < (g + 1) * m : nat.mul_lt_mul_of_pos_right (lt_add_one g) h0m
      ... ≤ (g + 1) * n : nat.mul_le_mul le_rfl hmn, },
    { apply smul_left_injective Λ h0n.ne', dsimp,
      rwa [← H, ← hgl₀, ← mul_nsmul, nat.mul_div_cancel', mul_nsmul], } }
end

lemma star_finite (hs : s.finite) : (star s).finite :=
by { rw star_eq_Union_star_singleton, exact hs.bind (λ _ _, star_singleton_finite _) }

end star

lemma filtration_finite (ε : ℝ≥0) : (filtration Λ ε).finite :=
begin
  classical,
  obtain ⟨ι, _ι_inst, l, hl, hl'⟩ := polyhedral_lattice.polyhedral Λ, resetI,
  let n : ι → ℕ := λ i, ⌈(ε / nnnorm (l i) : ℝ)⌉.nat_abs + 1,
  let S := finset.univ.pi (λ i, finset.range (n i)),
  let S' : finset Λ := S.image (λ x, ∑ i, x i (finset.mem_univ _) • l i),
  apply (star_finite _ S'.finite_to_set).subset,
  intros l₀ hl₀,
  obtain ⟨d, hd, c, h1, h2⟩ := hl l₀,
  refine ⟨_, 1, d, _, zero_lt_one, hd, (one_smul _ _).trans h1.symm⟩,
  simp only [S', set.mem_image, finset.mem_univ, finset.mem_pi, forall_true_left, finset.mem_range,
    finset.mem_coe, finset.coe_image],
  refine ⟨λ i _, c i, _, rfl⟩,
  rintro i -,
  rw finset.mem_range,
  apply nat.succ_le_succ,
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
