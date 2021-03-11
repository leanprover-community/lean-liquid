import system_of_complexes.double
import system_of_complexes.soft_truncation

noncomputable theory
open_locale nnreal
open system_of_double_complexes category_theory

universe variables u

@[simps]
def shift_and_truncate : system_of_double_complexes.{u} ⥤ system_of_double_complexes.{u} :=
(whiskering_right _ _ _).obj $
  @functor.map_complex_like _ _ _ _ _ _ _ _ _ _ NormedGroup.shift_and_truncate.additive.{u u}
-- TODO: why do I need to give the instance manually? ↑ ↑ ↑

namespace shift_and_truncate

variables (M : system_of_double_complexes.{u})

lemma admissible (hM : M.admissible) : (shift_and_truncate.obj M).admissible :=
{ d_norm_noninc' := sorry,
  d'_norm_noninc' := sorry,
  res_norm_noninc := sorry }

-- defeq abuse for the win!!!
lemma row (p : ℤ) :
  (shift_and_truncate.obj M).row p = system_of_complexes.shift_and_truncate.obj (M.row p) := rfl

end shift_and_truncate

-- move this, better name?
lemma norm_le_add_norm_add {V : Type*} [normed_group V] (x y : V) :
  ∥x∥ ≤ ∥x + y∥ + ∥y∥ :=
calc ∥x∥ = ∥x + y - y∥ : by rw add_sub_cancel
... ≤ ∥x + y∥ + ∥y∥ : norm_sub_le _ _

/-- The assumptions on `M` in Proposition 9.6 bundled into a structure. Note that in `cond3b`
  our `q` is one smaller than the `q` in the notes (so that we don't have to deal with `q - 1`). -/
structure normed_spectral_conditions (m : ℤ) (k K : ℝ≥0) [fact (1 ≤ k)]
  (ε : ℝ) (hε : 0 < ε) (M : system_of_double_complexes.{u})
  (k' : ℝ≥0) [fact (1 ≤ k')] (c₀ H : ℝ≥0) [fact (0 < H)] :=
(col_exact : ∀ j ≤ m, (M.col j).is_weak_bounded_exact k K m c₀)
(row_exact : ∀ i ≤ m + 1, (M.row i).is_weak_bounded_exact k K (m-1) c₀)
(h : Π (q : ℤ) {q' : ℤ} {c}, M.X (k' * c) 0 q' ⟶ M.X c 1 q)
(norm_h_le : ∀ (q' q : ℤ) (hq : q ≤ m) (hq' : q+1 = q') (c) (hc : c₀ ≤ c)
  (x : M.X (k' * c) 0 q'), ​∥h q x∥ ≤ H * ∥x∥)
-- do we have a better name for the following condition?
(cond3b : ∀ (q'' q' q : ℤ) (hq'' : q'+1 = q'') (hq' : q+1 = q') (hq : q+1 ≤ m) (c) [fact (c₀ ≤ c)]
  (x : M.X (k' * (k' * c)) 0 q') (u1 u2 : units ℤ),
  ​∥M.res (M.d 0 1 x) + (u1:ℤ) • h q' (M.d' q' q'' x) + (u2:ℤ) • M.d' q q' (h q x)∥ ≤
    ε * ∥(res M x : M.X c 0 q')∥)
-- ergonomics: we bundle this assumption, instead of passing it around separately
(admissible : M.admissible)
-- the following 3 conditions are automatic in [Analytic.pdf],
-- but we need them, because our complexes are indexed by `ℤ`
(Hneg : (M.row 0).is_weak_bounded_exact (k' * k') (2 * K * H) (-1) c₀)
(Hd : ∀ c q (x : M.X c (-1) q), M.d _ 0 x = 0)
(Hd' : ∀ c p (x : M.X c p (-1)), M.d' _ 0 x = 0)

.

namespace normed_spectral_conditions

variables {m' m : ℤ} {k K : ℝ≥0} [fact (1 ≤ k)]
variables {ε : ℝ} {hε : 0 < ε} {k₀ : ℝ≥0} [fact (1 ≤ k₀)]
variables {M : system_of_double_complexes.{u}}
variables {k' : ℝ≥0} [fact (k₀ ≤ k')] [fact (1 ≤ k')] {c₀ H : ℝ≥0} [fact (0 < H)]

lemma shift_and_truncate_admissible (cond : normed_spectral_conditions m k K ε hε M k' c₀ H) :
  (shift_and_truncate.obj M).admissible :=
shift_and_truncate.admissible _ cond.admissible

def shift_and_truncate (cond : normed_spectral_conditions m k K ε hε M k' c₀ H) (h : m' + 1 = m) :
  normed_spectral_conditions m' (k*k*k) (K*(K*K+1)) ε hε (shift_and_truncate.obj M) k' c₀ H :=
{ col_exact := sorry,
  row_exact :=
  begin
    intros i hi,
    suffices : ((shift_and_truncate.obj M).row i).is_weak_bounded_exact k K (m' - 1) c₀,
    { apply this.of_le _ _ _ le_rfl le_rfl,
      { exact cond.shift_and_truncate_admissible.row i },
      { show fact (k ≤ k * k * k), apply_instance },
      { show fact (K ≤ K * (K * K + 1)), sorry } },
    rw ← eq_sub_iff_add_eq at h, subst m', rw sub_add_cancel at hi,
    rw shift_and_truncate.row,
    apply (M.row i).shift_and_truncate_is_weak_bounded_exact,
    { exact cond.row_exact i (int.le_add_one hi) },
    { exact sub_add_cancel _ _ }
  end,
  h := sorry,
  norm_h_le := sorry,
  cond3b := sorry,
  admissible := cond.shift_and_truncate_admissible,
  Hneg := sorry,
  Hd := sorry,
  Hd' := sorry }

end normed_spectral_conditions

/-- Base case of the induction for Proposition 9.6. -/
theorem analytic_9_6_base (k K : ℝ≥0) [hk : fact (1 ≤ k)] [hK : fact (1 ≤ K)] :
  ∃ (ε : ℝ) (hε : ε > 0) (k₀ : ℝ≥0) [fact (1 ≤ k₀)],
  ∀ (M : system_of_double_complexes.{u})
    (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] -- follows
    (c₀ H : ℝ≥0) [fact (0 < H)],
  ​∀ (cond : normed_spectral_conditions 0 k K ε hε M k' c₀ H),
  (M.row 0).is_weak_bounded_exact (k' * k') (2 * K * H) 0 c₀ :=
begin
  let ε := (2*K)⁻¹,
  have hε : 0 < ε,
  { exact nnreal.inv_pos.mpr (mul_pos zero_lt_two (lt_of_lt_of_le zero_lt_one hK)) },
  use [ε, hε, k, hk],
  introsI M k' _k' _1k' c₀ H _H cond,
  intros c hc i hi,
  cases le_or_lt i (-1 : ℤ) with h h,
  { exact cond.Hneg c hc i h },
  -- Statement is of the form "for all x ∈ M_{0,i+1} exists y ∈ M_{0,i} such that..."
  interval_cases i, clear hi h,
  intros x δ hδ,
  haveI : fact (k' * (k' * c) ≤ k' * k' * c) := by { rw mul_assoc, exact le_rfl },
  have Hx1 := (cond.col_exact 0 le_rfl).of_le
    (cond.admissible.col 0) _k' le_rfl le_rfl le_rfl c hc 0 le_rfl,
  have Hx2 := cond.cond3b,
  replace Hx2 := @Hx2 1 0 (-1) rfl rfl le_rfl c hc (M.res x) 1 1,
  simp only [row_d, col_d, cond.Hd, cond.Hd', sub_zero, add_zero, smul_zero, d_res, d'_res,
    res_res, one_div, row_res, units.coe_one, one_smul] at Hx1 Hx2 ⊢,
  refine ⟨-1, 1, rfl, rfl, 0, _⟩,
  let φ : ℝ := δ / 2,
  have hφ : 0 < φ := div_pos hδ zero_lt_two,
  have hδφ : δ = φ + φ, { dsimp [φ], rw [← add_div, half_add_self] },
  obtain ⟨i, j, hi, hj, y1, hx1⟩ := Hx1 (M.res x) φ hφ,
  simp [← eq_neg_iff_add_eq_zero] at hi hj, subst i, subst j,
  simp only [cond.Hd, cond.Hd', sub_zero,
    nnreal.coe_mul, nnreal.coe_bit0, nnreal.coe_one, d_res] at hx1 ⊢,
  erw [res_res] at hx1,
  clear y1 Hx1,
  replace Hx1 := mul_le_mul_of_nonneg_left hx1 ε.coe_nonneg,
  replace Hx2 := (norm_le_add_norm_add _ _).trans (add_le_add (Hx2.trans Hx1) le_rfl),
  dsimp [ε] at Hx2,
  have K0 : (K:ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK),
  simp only [mul_add, add_assoc, mul_inv', mul_assoc, inv_mul_cancel_left' K0] at Hx2,
  simp only [← div_eq_inv_mul, sub_half, ← sub_le_iff_le_add'] at Hx2,
  simp only [sub_le_iff_le_add', div_le_iff' (zero_lt_two : (0:ℝ) < 2)] at Hx2,
  replace Hx2 := mul_le_mul_of_nonneg_left Hx2 K.coe_nonneg,
  simp only [mul_add, div_eq_inv_mul, add_comm φ,
    mul_inv_cancel_left' (two_ne_zero : (2:ℝ) ≠ 0), mul_inv_cancel_left' K0] at Hx2,
  refine hx1.trans _,
  simp only [mul_comm (2:ℝ) K, mul_assoc, hδφ, ← add_assoc, ← mul_add, add_le_add_iff_right],
  refine Hx2.trans _,
  simp only [add_le_add_iff_right],
  refine (mul_le_mul_of_nonneg_left _ K.coe_nonneg),
  refine (mul_le_mul_of_nonneg_left _ zero_le_two),
  refine le_trans (cond.norm_h_le _ _ le_rfl rfl _ _ _) _,
  { calc c₀ = 1 * c₀ : (one_mul c₀).symm
    ... ≤ k' * c : mul_le_mul' _1k' hc },
  refine mul_le_mul_of_nonneg_left (le_of_eq _) H.coe_nonneg,
  apply norm_res_of_eq,
  rw mul_assoc
end

/-- Proposition 9.6 in [Analytic]
Constants (max (k' * k') (2 * k₀ * H)) and K in the statement are not the right ones.
We need to investigate the consequences of the k Zeeman effect here.
-/
theorem analytic_9_6 (m : ℤ) :
  ∀ (k K : ℝ≥0) [fact (1 ≤ k)] [hK : fact (1 ≤ K)],
  ∃ (ε : ℝ) (hε : ε > 0) (k₀ : ℝ≥0) [fact (1 ≤ k₀)],
  ∀ (M : system_of_double_complexes.{u})
    (k' : ℝ≥0) [fact (k₀ ≤ k')] [fact (1 ≤ k')] -- follows
    (c₀ H : ℝ≥0) [fact (0 < H)],
  ​∀ (cond : normed_spectral_conditions m k K ε hε M k' c₀ H),
  (M.row 0).is_weak_bounded_exact (k' * k') (2 * K * H) m c₀ :=
begin
  apply int.induction_on m,
  -- induction m with m hm,
  { -- base case m = 0
    exact analytic_9_6_base, },
  swap, -- deal with the pesky m < 0
  { intro m, intros, refine ⟨1, zero_lt_one, 1, le_rfl, _⟩,
    introsI,
    intros c hc i hi,
    refine cond.Hneg c hc i _,
    have : 0 ≤ (m : ℤ) := int.coe_zero_le m,
    rw ← zero_sub,
    exact hi.trans (sub_le_sub (neg_le.mp this) le_rfl) },
  { -- inductive step
    sorry }
end
