import system_of_complexes.double

open_locale nnreal
open system_of_double_complexes

universe variables u

/-- The assumptions on `M` in Proposition 9.6 bundled into a structure. Note that in `cond3b`
  our `q` is one smaller than the `q` in the notes (so that we don't have to deal with `q - 1`). -/
structure normed_spectral_conditions (m : ℕ) (k K : ℝ≥0) [fact (1 ≤ k)]
  (ε : ℝ) (hε : 0 < ε) (k₀ : ℝ≥0) [fact (1 ≤ k₀)]
  (M : system_of_double_complexes)
  (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] (c₀ H : ℝ≥0) [fact (0 < H)] :=
(col_exact : ∀ j ≤ m, (M.col j).is_bounded_exact k K (m+1) c₀)
(row_exact : ∀ i ≤ m + 1, (M.row i).is_bounded_exact k K m c₀)
(h : Π {q : ℤ} [fact (q ≤ m)] {c} [fact (c₀ ≤ c)], M.X (k' * c) 0 (q+1) ⟶ M.X c 1 q)
(norm_h_le : ∀ (q : ℤ) [fact (q ≤ m)] (c) [fact (c₀ ≤ c)] (x : M.X (k' * c) 0 (q+1)), ​∥h x∥ ≤ H * ∥x∥)
(cond3b : ∀ (q : ℤ) [fact (q+1 ≤ m)] (c) [fact (c₀ ≤ c)]
  (x : M.X (k' * (k' * c)) 0 (q+1)) (u1 u2 : units ℤ),
  ​∥M.res (M.d x) + (u1:ℤ) • h (M.d' x) + (u2:ℤ) • M.d' (h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥)
.

namespace normed_spectral_conditions

variables (m : ℕ) (k K : ℝ≥0) [fact (1 ≤ k)]
variables (ε : ℝ) (hε : 0 < ε) (k₀ : ℝ≥0) [fact (1 ≤ k₀)]
variables (M : system_of_double_complexes.{u})
variables (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] (c₀ H : ℝ≥0) [fact (0 < H)]

lemma cond3bpp (NSC : normed_spectral_conditions.{u u} m k K ε hε k₀ M k' c₀ H)
  (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
  ​∥M.res (M.d x) + NSC.h (M.d' x) + M.d' (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
by simpa only [units.coe_one, one_smul] using NSC.cond3b q c x 1 1

lemma cond3bpm (NSC : normed_spectral_conditions.{u u} m k K ε hε k₀ M k' c₀ H)
  (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
  ​∥M.res (M.d x) + NSC.h (M.d' x) - M.d' (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
by simpa only [units.coe_one, one_smul, neg_smul, units.coe_neg, ← sub_eq_add_neg]
  using NSC.cond3b q c x 1 (-1)

lemma cond3bmp (NSC : normed_spectral_conditions.{u u} m k K ε hε k₀ M k' c₀ H)
  (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
  ​∥M.res (M.d x) - NSC.h (M.d' x) + M.d' (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
by simpa only [units.coe_one, one_smul, neg_smul, units.coe_neg, ← sub_eq_add_neg]
  using NSC.cond3b q c x (-1) 1

lemma cond3bmm (NSC : normed_spectral_conditions.{u u} m k K ε hε k₀ M k' c₀ H)
  (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
  ​∥M.res (M.d x) - NSC.h (M.d' x) - M.d' (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
by simpa only [units.coe_one, one_smul, neg_smul, units.coe_neg, ← sub_eq_add_neg]
  using NSC.cond3b q c x (-1) (-1)

end normed_spectral_conditions

/-- Proposition 9.6 in [Analytic]
Constants (max (k' * k') (2 * k₀ * H)) and K in the statement are not the right ones.
We need to investigate the consequences of the k Zeeman effect here.
-/
theorem analytic_9_6 (m : ℕ) (k K : ℝ≥0) [fact (1 ≤ k)] :
  ∃ (ε : ℝ) (hε : ε > 0) (k₀ : ℝ≥0) [fact (1 ≤ k₀)],
  ∀ (M : system_of_double_complexes) (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] -- follows
    (c₀ H : ℝ≥0) [fact (0 < H)],
  ​∀ (Hneg : (M.row 0).is_bounded_exact (max (k' * k') (2 * k₀ * H)) K (-1) c₀)
    (Hd : ∀ c q (x : M.X c (-1) q), M.d x = 0)
    (Hd' : ∀ c p (x : M.X c p (-1)), M.d' x = 0)
    (cond : normed_spectral_conditions m k K ε hε k₀ M k' c₀ H),
  (M.row 0).is_bounded_exact (max (k' * k') (2 * k₀ * H)) K (m+1) c₀ :=
begin
  induction m with m hm,
  { -- base case m = 0
    -- ε = 1/(2k) works
    use [1/(2*k)],
    existsi _, swap,
    { have hk : 1 ≤ k := fact.elim (by apply_instance),
      rw [gt_iff_lt, one_div, inv_pos],
      refine mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (by assumption_mod_cast)) },
    -- k₀ = k works
    use k,
    use (by assumption),
    introsI M k' _k' _1k' c₀ H _H Hneg Hd Hd' cond,
    intros c hc i hi x,
    change i < 1 at hi,
    -- Statement is of the form "for all x ∈ M_{0,i+1} exists y ∈ M_{0,i} such that..."
    -- Cases i<-1 are trivial because x=y=0 works.
    cases lt_or_le i (-1 : ℤ) with h h,
    { -- this should deal with -1
      exact Hneg c hc i h x },
    -- cases i = -1 and i = 0 left
    interval_cases i,
    { sorry },
    { sorry }
  },
  { -- inductive step
    sorry }
end
