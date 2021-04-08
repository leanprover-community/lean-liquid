import analysis.specific_limits

import for_mathlib.normed_group

open finset filter
open_locale big_operators topological_space uniformity

variables {G : Type*} [normed_group G]
          {H : Type*} [normed_group H]

lemma normed_group.cauchy_seq_of_le_geometric {C : ℝ} {r : ℝ} (hr : r < 1)
    {u : ℕ → G} (h : ∀ n, ∥u n - u (n + 1)∥ ≤ C*r^n) : cauchy_seq u :=
begin
  apply cauchy_seq_of_le_geometric _ C hr,
  simpa [dist_eq_norm] using h
end

lemma normed_group.cauchy_series_of_le_geometric {C : ℝ} {u : ℕ → G}
  {r : ℝ} (hr : r < 1)
  (h : ∀ n, ∥u n∥ ≤ C*r^n) : cauchy_seq (λ n, ∑ k in range n, u k) :=
begin
  apply normed_group.cauchy_seq_of_le_geometric hr,
  intro n,
  rw [show ∑ k in range n, u k - ∑ k in range (n + 1), u k = - u n,
        by { simp only [finset.sum_range_succ], abel}, norm_neg],
  apply h
end

lemma normed_group.cauchy_series_of_le_geometric' {C : ℝ} {u : ℕ → G} {r : ℝ} (hr : r < 1)
  (h : ∀ n, ∥u n∥ ≤ C*r^n) : cauchy_seq (λ n, ∑ k in range (n + 1), u k) :=
begin
  by_cases hC : C = 0,
  { subst hC,
    simp at h,
    simp [h, cauchy_seq_const (0 : G)] },
  have : 0 ≤ C,
  { simpa using (norm_nonneg _).trans (h 0) },
  replace hC : 0 < C,
    from (ne.symm hC).le_iff_lt.mp this,
  have : 0 ≤ r,
  { have := (norm_nonneg _).trans (h 1),
    rw pow_one at this,
    exact (zero_le_mul_left hC).mp this },
  simp_rw finset.sum_range_succ_comm,
  have : cauchy_seq u,
  { apply tendsto.cauchy_seq,
    apply squeeze_zero_norm h,
    rw show 0 = C*0, by simp,
    exact tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 this hr) },
  exact this.add (normed_group.cauchy_series_of_le_geometric hr h),
end

lemma normed_group.cauchy_series_of_le_geometric'' {C : ℝ} {u : ℕ → G} {N : ℕ} {r : ℝ}
  (hr₀ : 0 < r) (hr₁ : r < 1)
  (h : ∀ n ≥ N, ∥u n∥ ≤ C*r^n) : cauchy_seq (λ n, ∑ k in range (n + 1), u k) :=
begin
  set v : ℕ → G := λ n, if n < N then 0 else u n,
  have hC : 0 ≤ C,
    from (zero_le_mul_right $ pow_pos hr₀ N).mp ((norm_nonneg _).trans $ h N $ le_refl N),
  have : ∀ n ≥ N, u n = v n,
  { intros n hn,
    simp [v, hn, if_neg (not_lt.mpr hn)] },
  refine cauchy_seq_of_eventually_eq this (normed_group.cauchy_series_of_le_geometric' hr₁ _),
  { exact C },
  intro n,
  dsimp [v],
  split_ifs with H H,
  { rw norm_zero,
    exact mul_nonneg hC (pow_nonneg hr₀.le _) },
  { push_neg at H,
    exact h _ H }
end
