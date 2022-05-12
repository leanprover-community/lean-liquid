import data.real.nnreal -- non-negative reals
import topology.algebra.infinite_sum -- infinite sums
import analysis.special_functions.log.basic
import analysis.special_functions.pow
import for_mathlib.nnreal

open_locale nnreal -- notation for non-negative reals

open_locale big_operators -- notation for infinite sums
/-

# Binary stuff

Binary expansion of `nnreal` works great. If `r : ℝ≥0` then you get a
`digits` function `d(r) : ℕ → ℕ` with `d(0)=⌊r⌋₊` and all the `d(n.succ)`
are 0 or 1, and the theorem is that `r = ∑ n, 2⁻¹ ^ n * b n`.

TODO : relationship between `binary r`
and `binary (2 * r)` or `binary (2⁻¹ * r)`?

-/

/-

## Random stuff

-/

-- move
lemma two_mul_lt_two {r : ℝ≥0} (hr : r < 1) : 2 * r < 2 :=
begin
  suffices : 2 * r < 2 * 1, by simpa,
  exact (mul_lt_mul_left (by norm_num)).mpr hr,
end

-- probably true in more generality than nnreal.
lemma nnreal.tsub_lt {a b c : ℝ≥0} (hc : c ≠ 0) (h : a < b + c) : a - b < c :=
begin
  cases le_or_lt a b with hab hab,
  { rw tsub_eq_zero_of_le hab,
    exact zero_lt_iff.mpr hc },
  { rwa tsub_lt_iff_left hab.le },
end

lemma nnreal.inv_pos_le_iff_one_le_mul {a b : ℝ≥0} (ha : 0 < a) : (a⁻¹ ≤ b ↔ 1 ≤ b * a) :=
begin
  suffices : (a : ℝ)⁻¹ ≤ b ↔ (1 : ℝ) ≤ b * a,
    assumption_mod_cast,
  rw inv_pos_le_iff_one_le_mul,
  assumption_mod_cast,
end


/-

# binary

An auxiliary function which computes the digits and remainders in the binary
expanion of a non-negative real.

-/

/-- An auxiliary function which computes binary expansion of a non-negative real
and also carries around the remainder. -/
noncomputable def nnreal.nat.binary (r : ℝ≥0) : ℕ → (ℕ × (ℝ≥0))
| 0 := (⌊r⌋₊, r - ⌊r⌋₊)
| (n + 1) := let digit := if (nnreal.nat.binary n).2 < 2⁻¹ then 0 else 1 in
             (digit, 2 * (nnreal.nat.binary n).2 - (digit : ℝ≥0))

namespace nnreal

namespace nat

/-

would be nice to turn on computable reals mode with same notation


binary_aux 0.15
(0,0.15)
(0,0.3)
(0,0.6)
(1,0.2)
(0,0.4)
(0,0.8)
(1.0.6)
(1,1.2)
(1,0.4)

binary_aux 23.45
(23,0.45)
(0,0.9)
(1,0.8)

-/

namespace binary

variables (r : ℝ≥0) (n : ℕ)

lemma zero_def : binary r 0 = (⌊r⌋₊,r - ⌊r⌋₊) :=
binary.equations._eqn_1 r

/-- This is the units digit -/
lemma zero_fst_def : (binary r 0).1 = ⌊r⌋₊ := by rw zero_def

lemma zero_fst_le : ((binary r 0).1 : ℝ≥0) ≤ r :=
begin
  rw zero_fst_def,
  apply nat.floor_le,
  exact coe_nonneg r,
end

lemma zero_snd_def : (binary r 0).2 = r - (binary r 0).1 :=
begin
  rw zero_def,
end


lemma succ_fst_def : (binary r (n + 1)).1 = if (binary r n).2 < 2⁻¹ then 0 else 1 :=
by rw binary.equations._eqn_2

lemma succ_fst_le :
  ((binary r (n + 1)).1 : ℝ≥0) ≤ 2 * (binary r n).2 :=
begin
  rw succ_fst_def,
  split_ifs,
  { simp },
  { push_neg at h,
    norm_cast,
    rw inv_pos_le_iff_one_le_mul at h, swap, norm_num,
    rwa mul_comm, },
end

lemma succ_snd_def : (binary r (n + 1)).2 = 2 * (binary r n).2 - (binary r (n + 1)).1 :=
by rw binary.equations._eqn_2

/-- A slightly mathematically stronger version of `succ_snd_def`. -/
lemma succ_snd_def' :
  (binary r (n + 1)).2 + (binary r (n + 1)).1 = 2 * ((binary r n).2 ) :=
begin
  rw succ_snd_def r n,
  exact tsub_add_cancel_of_le (succ_fst_le r n),
end

-- note: the zeroth digit can be any natural.
theorem succ_fst_le_one : (binary r (n + 1)).1 ≤ 1 :=
begin
  rw succ_fst_def,
  split_ifs; linarith,
end

/-- The remainder is bounded. -/
lemma snd_bdd : (binary r n).2 < 1 :=
begin
  induction n with d hd,
  { simp [zero_def],
    have := nat.lt_floor_add_one r,
    have foo : (⌊r⌋₊ : ℝ≥0) ≤ r := nat.floor_le (zero_le'),
    exact (tsub_lt_iff_left foo).mpr this, },
  { simp only [succ_snd_def, succ_fst_def, nat.cast_ite, nat.cast_zero, nat.cast_one],
    split_ifs with LEM,
    { simp,
      rw ← mul_lt_mul_left (show (0 : ℝ≥0) < 2, by norm_num) at LEM,
      convert LEM,
      simp },
    { push_neg at LEM,
      revert hd,
      generalize hx : (binary r d).snd = x, rw hx at LEM, clear hx,
      intro hx,
      rw [← mul_lt_mul_left (show (0 : ℝ≥0) < 2, by norm_num), mul_one] at hx,
      apply nnreal.tsub_lt, norm_num,
      convert hx, }, },
end

lemma fund_thm (B : ℕ) :
  ∑ n in finset.range B.succ, ((binary r n).1 : ℝ≥0) * 2⁻¹ ^ n +
    (binary r B).2 * 2⁻¹ ^ B = r :=
begin
  induction B with d hd,
  { simp only [zero_snd_def, zero_fst_def, finset.range_one, finset.sum_singleton,
      pow_zero, mul_one],
    rw ← add_tsub_assoc_of_le, swap, apply nat.floor_le, apply zero_le,
    exact add_tsub_cancel_left ↑⌊r⌋₊ r, },
  { rw [finset.sum_range_succ, add_assoc],
    convert hd,
    rw [← add_mul, add_comm, succ_snd_def', nat.succ_eq_add_one, pow_add, pow_one],
    rw [mul_comm (2 : ℝ≥0), mul_assoc],
    congr',
    rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one],
    norm_num, }
end

lemma fund_thm' (B : ℕ) :
  (binary r B).2 + (∑ n in finset.range B.succ, ((binary r n).1 * 2 ^ (B - n)) : ℕ) = r * 2 ^ B :=
begin
  have := fund_thm r B,
  apply_fun (λ x, x * (2 : ℝ≥0) ^ B) at this,
  convert this,
  rw [add_comm, add_mul],
  congr',
  { rw finset.sum_mul,
    push_cast,
    apply finset.sum_congr rfl, intros n hn,
    rw finset.mem_range_succ_iff at hn,
    rw [mul_assoc, zero_add, one_add_one_eq_two],
    congr',
    simp,
    rw [pow_sub₀ (2 : ℝ≥0) _ hn, mul_comm],
    norm_num, },
  { rw [mul_assoc, ← mul_pow, inv_mul_cancel],
    { simp, },
    { norm_num }, },
end

end binary

-- in `nnreal` namespace
noncomputable def digit (r : ℝ≥0) (n : ℕ) : ℕ := (binary r n).1

namespace digit

variables (r : ℝ≥0) (n B : ℕ)

lemma zero_def : digit r 0 = ⌊r⌋₊ := binary.zero_fst_def r

lemma zero_le : (digit r 0 : ℝ≥0) ≤ r :=
binary.zero_fst_le r

theorem succ_le_one : (digit r (n + 1)) ≤ 1 :=
binary.succ_fst_le_one r n

theorem sum_le_r : ∑ n in finset.range B.succ, ((digit r n) : ℝ≥0) * 2⁻¹ ^ n ≤ r :=
begin
  conv_rhs {rw ← binary.fund_thm r B},
  apply le_add_right,
  refl,
end

theorem r_le_pow_add_sum :
  r < 2⁻¹ ^ B + ∑ n in finset.range B.succ, ((digit r n) : ℝ≥0) * 2⁻¹ ^ n :=
begin
  conv_lhs {rw ← binary.fund_thm r B},
      rw add_comm,
    refine add_lt_add_right _ _,
    rw mul_lt_iff_lt_one_left,
    { exact binary.snd_bdd r B },
    { apply pow_pos,
      norm_num, },
end

lemma r_sub_sum_small : r - ∑ n in finset.range B.succ, ((digit r n) : ℝ≥0) * 2⁻¹ ^ n < 2⁻¹ ^ B :=
begin
  have := r_le_pow_add_sum r B,
  rw ← tsub_lt_tsub_iff_right (sum_le_r r B) at this,
  convert this,
  simp,
end

--theorem r_bounds :
--   r ∈ set.Ico
--   (∑ n in finset.range B.succ, ((digit r n) : ℝ≥0) * 2⁻¹ ^ n)
--   (2⁻¹ ^ B + ∑ n in finset.range B.succ, ((binary r n).1 : ℝ≥0) * 2⁻¹ ^ n)
--   :=
-- ⟨sum_le_r r B, r_le_pow_add_sum r B⟩

theorem summable : summable (λ (n : ℕ), (nnreal.nat.digit r n : ℝ≥0) * 2⁻¹ ^ n) :=
begin
  have foo : ∀ n, (nnreal.nat.digit r n : ℝ≥0) ≤ max (nnreal.nat.digit r 0) 1,
  { rintro (rfl | n),
    { apply le_max_left, },
    { refine le_trans _ (le_max_right _ _),
      exact_mod_cast succ_le_one r n, }, },
  have bar : ∀ n, (nnreal.nat.digit r n : ℝ≥0) * 2⁻¹ ^ n ≤ max (nnreal.nat.digit r 0) 1 * 2⁻¹ ^ n,
  { intro n,
    rw mul_le_mul_right₀, exact foo n,
    apply pow_ne_zero,
    norm_num, },
  apply summable_of_le bar,
  apply summable.mul_left,
  apply summable_geometric,
  apply two_inv_lt_one,
end

theorem has_sum : has_sum (λ n, (digit r n : ℝ≥0) * 2⁻¹ ^ n) r :=
begin
  rw summable.has_sum_iff_tendsto_nat (summable r),
  dsimp,
  intros X hX,
  rw mem_nhds_iff at hX,
  rcases hX with ⟨V, hVX, hV1, hVr⟩,
  rw filter.mem_map,
  rw filter.mem_at_top_sets,
  -- choose a large enough such that (r-2⁻¹^a,r] ⊆ V
  obtain ⟨ε, hε, hεV⟩ := metric.is_open_iff.mp hV1 r hVr,
  change 0 < ε at hε,
  have foo : ∃ a : ℕ, (2⁻¹ : ℝ≥0) ^ a ≤ ⟨ε, hε.le⟩,
  { by_cases hε1 : 1 ≤ ε,
    { use 0, simp, exact_mod_cast hε1, },
    { push_neg at hε1,
      use ⌈real.log ε / real.log 2⁻¹⌉₊,
      have := nat.le_ceil (real.log ε / real.log 2⁻¹),
      have moo : (2⁻¹ : ℝ≥0) ^ (↑⌈real.log ε / real.log 2⁻¹⌉₊) ≤
        2⁻¹ ^ (real.log ε / real.log 2⁻¹),
      exact rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) this,
      convert le_trans moo _ using 1, norm_cast,
      -- now coerce to real
      suffices : (2⁻¹ : ℝ) ^ (real.log ε / real.log 2⁻¹) ≤ ε,
        assumption_mod_cast,
      -- convenient thing
      have inv_two_pos : (0 : ℝ) < 2⁻¹,
      { rw _root_.inv_pos, apply zero_lt_two, },
      rw ← real.log_le_log (real.rpow_pos_of_pos inv_two_pos _) hε,
      apply le_of_eq,
      rw real.log_rpow inv_two_pos,
      rw div_mul_cancel,
      apply real.log_ne_zero_of_pos_of_ne_one inv_two_pos,
      norm_num, } },
  cases foo with B hB,
  use B + 1,
  intros m hm, cases m with m, cases hm,
  rw set.mem_preimage,
  have h_le_r := sum_le_r r m,
  have h_r_lt := r_le_pow_add_sum r m,
  apply hVX,
  apply hεV,
  rw metric.mem_ball,
  change |_ - _| < ε,
  rw abs_lt,
  rw ← nnreal.coe_lt_coe at h_r_lt,
  push_cast at h_r_lt ⊢,
  split,
  { suffices : (2⁻¹ : ℝ) ^ m ≤ ε,
      linarith,
    have hB' : (2⁻¹ : ℝ) ^ B ≤ ε, assumption_mod_cast,
    refine le_trans _ hB',
    refine pow_le_pow_of_le_one (by norm_num) (by norm_num) _,
    change B + 1 ≤ m + 1 at hm,
    linarith,
  },
  { rw ← nnreal.coe_le_coe at h_le_r,
    push_cast at h_le_r,
    linarith,
  }
end

theorem tsum : ∑' n, (digit r n : ℝ≥0) * 2⁻¹ ^ n = r :=
has_sum.tsum_eq (has_sum r)

end digit

end nat

end nnreal
