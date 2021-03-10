import system_of_complexes.double
import system_of_complexes.soft_truncation

open_locale nnreal
open system_of_double_complexes

universe variables u

-- def shift_and_truncate : system_of_double_complexes ⥤ system_of_double_complexes :=
-- sorry

/-- The assumptions on `M` in Proposition 9.6 bundled into a structure. Note that in `cond3b`
  our `q` is one smaller than the `q` in the notes (so that we don't have to deal with `q - 1`). -/
structure normed_spectral_conditions (m : ℤ) (k K : ℝ≥0) [fact (1 ≤ k)]
  (ε : ℝ) (hε : 0 < ε) (k₀ : ℝ≥0) [fact (1 ≤ k₀)]
  (M : system_of_double_complexes.{u})
  (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] (c₀ H : ℝ≥0) [fact (0 < H)] :=
(col_exact : ∀ j ≤ m, (M.col j).is_bounded_exact k K m c₀)
(row_exact : ∀ i ≤ m + 1, (M.row i).is_bounded_exact k K (m-1) c₀)
(h : Π (q : ℤ) {q' : ℤ} {c}, M.X (k' * c) 0 q' ⟶ M.X c 1 q)
(norm_h_le : ∀ (q' q : ℤ) (hq : q ≤ m) (hq' : q+1 = q') (c) [fact (c₀ ≤ c)]
  (x : M.X (k' * c) 0 q'), ​∥h q x∥ ≤ H * ∥x∥)
(cond3b : ∀ (q'' q' q : ℤ) (hq'' : q'+1 = q'') (hq' : q+1 = q') (hq : q+1 ≤ m) (c) [fact (c₀ ≤ c)]
  (x : M.X (k' * (k' * c)) 0 q') (u1 u2 : units ℤ),
  ​∥M.res (M.d 0 1 x) + (u1:ℤ) • h q' (M.d' q' q'' x) + (u2:ℤ) • M.d' q q' (h q x)∥ ≤
    ε * ∥(res M x : M.X c 0 q')∥)
.

namespace normed_spectral_conditions

variables {m : ℤ} {k K : ℝ≥0} [fact (1 ≤ k)]
variables {ε : ℝ} {hε : 0 < ε} {k₀ : ℝ≥0} [fact (1 ≤ k₀)]
variables {M : system_of_double_complexes.{u}}
variables {k' : ℝ≥0} [fact (k₀ ≤ k')] [fact (1 ≤ k')] {c₀ H : ℝ≥0} [fact (0 < H)]

-- lemma cond3bpp (NSC : normed_spectral_conditions m k K ε hε k₀ M k' c₀ H)
--   (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
--   ​∥M.res (M.d _ _ x) + NSC.h (M.d' _ _ x) + M.d' _ _ (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
-- by simpa only [units.coe_one, one_smul] using NSC.cond3b q c x 1 1

-- lemma cond3bpm (NSC : normed_spectral_conditions m k K ε hε k₀ M k' c₀ H)
--   (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
--   ​∥M.res (M.d _ _ x) + NSC.h (M.d' _ _ x) - M.d' _ _ (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
-- by simpa only [units.coe_one, one_smul, neg_smul, units.coe_neg, ← sub_eq_add_neg]
--   using NSC.cond3b q c x 1 (-1)

-- lemma cond3bmp (NSC : normed_spectral_conditions m k K ε hε k₀ M k' c₀ H)
--   (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
--   ​∥M.res (M.d _ _ x) - NSC.h (M.d' _ _ x) + M.d' _ _ (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
-- by simpa only [units.coe_one, one_smul, neg_smul, units.coe_neg, ← sub_eq_add_neg]
--   using NSC.cond3b q c x (-1) 1

-- lemma cond3bmm (NSC : normed_spectral_conditions m k K ε hε k₀ M k' c₀ H)
--   (q : ℤ) [fact (q + 1 ≤ m)] (c : ℝ≥0) [fact (c₀ ≤ c)] (x : M.X (k' * (k' * c)) 0 (q+1)) :
--   ​∥M.res (M.d _ _ x) - NSC.h (M.d' _ _ x) - M.d' _ _ (NSC.h x)∥ ≤ ε * ∥(res M x : M.X c 0 (q+1))∥ :=
-- by simpa only [units.coe_one, one_smul, neg_smul, units.coe_neg, ← sub_eq_add_neg]
--   using NSC.cond3b q c x (-1) (-1)

end normed_spectral_conditions

/-- Base case of the induction for Proposition 9.6. -/
theorem analytic_9_6_base :
  ∀ (k K : ℝ≥0) [fact (1 ≤ k)],
  ∃ (ε : ℝ) (hε : ε > 0) (k₀ : ℝ≥0) [fact (1 ≤ k₀)],
  ∀ (M : system_of_double_complexes.{u}) (hM : M.admissible)
    (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] -- follows
    (c₀ H : ℝ≥0) [fact (0 < H)],
  ​∀ (Hneg : (M.row 0).is_bounded_exact (k' * k') (2 * k₀ * H) (-1) c₀)
    (Hd : ∀ c q (x : M.X c (-1) q), M.d _ 0 x = 0)
    (Hd' : ∀ c p (x : M.X c p (-1)), M.d' _ 0 x = 0)
    (cond : normed_spectral_conditions 0 k K ε hε k₀ M k' c₀ H),
  (M.row 0).is_bounded_exact (k' * k') (2 * k₀ * H) 0 c₀ :=
begin
  -- ε = 1/(2k) works
  introsI,
  use [1/(2*k)],
  existsi _, swap,
  { have hk : 1 ≤ k := fact.elim (by apply_instance),
    rw [gt_iff_lt, one_div, inv_pos],
    refine mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (by assumption_mod_cast)) },
  -- k₀ = k works
  use k,
  use (by assumption),
  introsI M hM k' _k' _1k' c₀ H _H Hneg Hd Hd' cond,
  intros c hc i hi,
  cases le_or_lt i (-1 : ℤ) with h h,
  { exact Hneg c hc i h },
  -- Statement is of the form "for all x ∈ M_{0,i+1} exists y ∈ M_{0,i} such that..."
  interval_cases i, clear hi h,
  intro x,
  haveI : fact (k' * (k' * c) ≤ k' * k' * c) := by { rw mul_assoc, exact le_rfl },
  have Hx1 := (cond.col_exact 0 le_rfl).of_le (hM.col 0) _k' le_rfl le_rfl le_rfl c hc 0 le_rfl,
  have Hx2 := cond.cond3b,
  replace Hx2 := @Hx2 1 0 (-1) rfl rfl le_rfl c hc (system_of_complexes.res x) 1 1,
  simp only [row_d, col_d, Hd, Hd', sub_zero, add_zero, smul_zero,
    res_res, one_div, row_res, units.coe_one, one_smul] at Hx1 Hx2 ⊢,
  refine ⟨-1, 1, rfl, rfl, 0, _⟩,
  obtain ⟨i, j, hi, hj, y1, hx1⟩ := Hx1 (system_of_complexes.res x),
  simp [← eq_neg_iff_add_eq_zero] at hi hj, subst i, subst j,
  simp only [Hd, Hd', sub_zero, res_res] at hx1 ⊢,
  sorry,
end

/-- Proposition 9.6 in [Analytic]
Constants (max (k' * k') (2 * k₀ * H)) and K in the statement are not the right ones.
We need to investigate the consequences of the k Zeeman effect here.
-/
theorem analytic_9_6 (m : ℤ) :
  ∀ (k K : ℝ≥0) [fact (1 ≤ k)],
  ∃ (ε : ℝ) (hε : ε > 0) (k₀ : ℝ≥0) [fact (1 ≤ k₀)],
  ∀ (M : system_of_double_complexes.{u}) (hM : M.admissible)
    (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] -- follows
    (c₀ H : ℝ≥0) [fact (0 < H)],
  ​∀ (Hneg : (M.row 0).is_bounded_exact (k' * k') (2 * k₀ * H) (-1) c₀)
    (Hd : ∀ c q (x : M.X c (-1) q), M.d _ 0 x = 0)
    (Hd' : ∀ c p (x : M.X c p (-1)), M.d' _ 0 x = 0)
    (cond : normed_spectral_conditions m k K ε hε k₀ M k' c₀ H),
  (M.row 0).is_bounded_exact (k' * k') (2 * k₀ * H) m c₀ :=
begin
  apply int.induction_on m,
  -- induction m with m hm,
  { -- base case m = 0
    exact analytic_9_6_base, },
  swap, -- deal with the pesky m < 0
  { intro m, intros, refine ⟨1, zero_lt_one, 1, le_rfl, _⟩,
    introsI,
    intros c hc i hi,
    refine Hneg c hc i _,
    have : 0 ≤ (m : ℤ) := int.coe_zero_le m,
    rw ← zero_sub,
    exact hi.trans (sub_le_sub (neg_le.mp this) le_rfl) },
  { -- inductive step
    sorry }
end
