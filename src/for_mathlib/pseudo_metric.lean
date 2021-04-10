import analysis.specific_limits

open finset

open_locale big_operators

lemma cauchy_seq_of_dist_le_of_summable_pseudo {α : Type*} [pseudo_metric_space α] {f : ℕ → α}
  (d : ℕ → ℝ) (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : summable d) : cauchy_seq f :=
begin
  refine metric.cauchy_seq_iff'.2 (λε εpos, _),
  replace hd : cauchy_seq (λ (n : ℕ), ∑ x in range n, d x) :=
    let ⟨_, H⟩ := hd in H.tendsto_sum_nat.cauchy_seq,
  refine (metric.cauchy_seq_iff'.1 hd ε εpos).imp (λ N hN n hn, _),
  have hsum := hN n hn,
  rw [real.dist_eq, ← sum_Ico_eq_sub _ hn] at hsum,
  calc dist (f n) (f N) = dist (f N) (f n) : dist_comm _ _
  ... ≤ ∑ x in Ico N n, d x : dist_le_Ico_sum_of_dist_le hn (λ k _ _, hf k)
  ... ≤ abs (∑ x in Ico N n, d x) : le_abs_self _
  ... < ε : hsum
end

lemma aux_has_sum_of_le_geometric_pseudo {α : Type*} [pseudo_metric_space α] {r C : ℝ} (hr : r < 1)
  {f : ℕ → α} (hu : ∀ (n : ℕ), dist (f n) (f (n + 1)) ≤ C * r ^ n) :
  has_sum (λ (n : ℕ), C * r ^ n) (C / (1 - r)) :=
begin
  rcases sign_cases_of_C_mul_pow_nonneg (λ n, dist_nonneg.trans (hu n)) with rfl | ⟨C₀, r₀⟩,
  { simp [has_sum_zero] },
  { refine has_sum.mul_left C _,
    simpa using has_sum_geometric_of_lt_1 r₀ hr }
end

lemma cauchy_seq_of_le_geometric_pseudo {α : Type*} [pseudo_metric_space α] (r C : ℝ) (hr : r < 1)
  {f : ℕ → α} (hu : ∀ (n : ℕ), dist (f n) (f (n + 1)) ≤ C * r ^ n) : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable_pseudo _ hu ⟨_, aux_has_sum_of_le_geometric_pseudo hr hu⟩
