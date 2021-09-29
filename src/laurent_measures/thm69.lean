import category_theory.Fintype
import data.real.nnreal
import laurent_measures.basic
import topology.basic
import order.filter.at_top_bot
import analysis.special_functions.exp_log


noncomputable theory

open set real (log) finset filter
open_locale topological_space nnreal big_operators filter classical

namespace thm71

section surjectivity

parameter (x : ℝ≥0)
variables (y : ℝ≥0) --(N : ℕ)

def N : ℕ := ⌈(x⁻¹ : ℝ)⌉₊

lemma N_inv_le : x ≥ 1 / N := sorry


--The minimal integer such that the corresponding coefficient in the Laurent series for y is ≠ 0
def deg : ℤ := ⌊(log y) / (log x)⌋

lemma xpow_le : x ^ (deg y) ≤ y := sorry

lemma deg_is_min : ∀ k < deg y, x ^ k > y := sorry

def a (m : ℤ) := ⌊ (y / x ^ m : ℝ)⌋₊

lemma a_bdd : a y (deg y) < N  := sorry

lemma y_mul_xpow_le : ((a y (deg y) : ℝ≥0) * x ^ (deg y)) ≤ y := sorry

def z (m : ℤ) := y - (a y m) * x ^ m

/--Given the bound L (eventually L = deg y), `step m` is the pair whose first element is the
(m+L)-th coefficient
-/
def step (L : ℤ) (m : ℕ) : ℕ × ℝ≥0 := (a y (L + m), z y (L + m))

noncomputable def A : ℕ → ℕ × ℝ≥0
| 0         := step y (deg y) 0
| (m + 1)   := step (A m).2 (deg y) (m + 1)--let z' := (A m).2, c := n y + m + 1 in (a z' c, z z' c)

lemma deg_increasing (k : ℕ) : deg (A y (k + 1)).2 > deg (A y k).2 := sorry

def coeff : ℤ → ℕ := λ k, if k < deg y then 0 else (A y (k + deg y ).to_nat).1

lemma surj_on_nonneg : has_sum (λ k : ℤ, (coeff y k : ℝ≥0) * x ^ k ) y := sorry

end surjectivity
end thm71

section fae_surjectivity

variables (ξ : ℝ) [fact (0 < ξ)] [fact (ξ < 1)]
variable (x : ℝ)

noncomputable def y : ℕ → ℝ
| 0         := x
| (n + 1)   := (y n) - (⌊(((y n) / ξ ^ n) : ℝ)⌋ : ℝ) * ξ ^ n


example (f : ℕ → ℝ) (h_mono : monotone f) :
  tendsto f at_top at_top ∨ (∃ l, tendsto f at_top (𝓝 l)) := tendsto_of_monotone h_mono


--[FAE] why I can't find this in mathlib?
lemma ge_of_div_le_one {a b : ℝ} (ha₁ : a ≥ 0) (hb₁ : b ≤ 1) (hb₂ : b > 0) : a ≤ a / b :=
begin
  by_cases ha : a > 0,
  { have that := (mul_le_mul_left ha).mpr ((one_le_div hb₂).mpr hb₁),
    rwa [← div_eq_mul_one_div, mul_one] at that },
  { simp only [gt_iff_lt, not_lt, ge_iff_le] at *,
    have : a = 0 := linarith.eq_of_not_lt_of_not_gt a 0 (not_lt_of_le ha₁) (not_lt_of_le ha),
    rw [this, zero_div] },
end

-- lemma eventually_le : ∀ n : ℕ, n ≥ 1 → (y ξ x n) ≤ ⌊(((y ξ x n) / ξ ^ n) : ℝ)⌋ :=
-- begin
--   intros n hn,
--   have h_pow : ξ ^ n ≤ 1, sorry,
--   -- have := (pow_lt_one_iff _).mpr (fact.out _) ξ,
--   -- have := (pow_lt_one_iff _).mpr
--   --   ((not_iff_not_of_iff (@nat.lt_one_iff n)).mp (not_lt_of_ge hn)),
--   -- -- sorry,
--   -- exact fact.out _,
--   calc y ξ x n ≤ (y ξ x n) / (ξ ^ n) : sorry--ge_of_div_le_one h_pow
--            ... ≤ ⌊(y ξ x n) / (ξ ^ n)⌋ : sorry,
-- end


lemma eventually_pos_y : ∀ n : ℕ, n ≥ 1 → y ξ x n ≥ 0 :=
begin
  have h_pos : ∀ n : ℕ, n ≥ 1 → ξ ^ n > 0 := λ n _, pow_pos (fact.out _) n,
  have : ∀ n : ℕ, n ≥ 1 →  (y ξ x n) / ξ ^ n ≥ ⌊(((y ξ x n) / ξ ^ n) : ℝ)⌋ := λ n _, floor_le _,
  intros n hn₁,
  by_cases hn₀ : n = 1,
  { rw [hn₀, y,pow_zero, div_one, mul_one, ge_iff_le, sub_nonneg], apply floor_le },
  { replace hn₁ : n > 1, {apply (lt_of_le_of_ne hn₁), tauto },
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m ≥ 1 ∧ n = m + 1,
    use ⟨n - 1, and.intro (nat.le_pred_of_lt hn₁) (nat.sub_add_cancel (le_of_lt hn₁)).symm⟩,
    rw [hm.2, y],
    replace this := (le_div_iff (h_pos m hm.1)).mp (this m hm.1),
    rwa ← sub_nonneg at this },
end

lemma eventually_pos_floor : ∀ n : ℕ, n ≥ 1 → (⌊((y ξ x n) / ξ ^ n )⌋ : ℝ) * ξ ^ n ≥ 0 :=
begin
  have h_pos : ∀ n : ℕ, n ≥ 1 → ξ ^ n > 0 := λ n _, pow_pos (fact.out _) n,
  intros n hn,
  apply mul_nonneg _ (le_of_lt (h_pos n hn)),
  norm_cast,
  apply floor_nonneg.mpr,
  exact div_nonneg (eventually_pos_y ξ x n hn) (le_of_lt (h_pos n hn)),
end

-- def dual_y := order_dual.to_dual ∘ (y ξ x)
def shift_y := λ n, y ξ x (n + 1)

#check shift_y ξ x
-- def dual_y : ℕ → (order_dual ℝ) := λ n, y ξ x n

lemma eventually_monotone : monotone (order_dual.to_dual ∘ (shift_y ξ x)) :=
-- lemma eventually_monotone : monotone (order_dual.to_dual ∘ (λ n : ℕ, y ξ x (n + 1))) :=
begin
  apply monotone_nat_of_le_succ,
  intro n,
  rw [@order_dual.dual_le ℝ _ _ _],
  by_cases hn : n ≥ 1,
  { replace hn : n + 1 ≥ 1 := by {simp only [ge_iff_le, zero_le', le_add_iff_nonneg_left] },
    exact sub_le_self (y ξ x (n + 1)) (eventually_pos_floor ξ x (n + 1) hn) },
  { replace hn : n = 0,
    rwa [not_le, nat.lt_one_iff] at hn,
    rw [hn, zero_add],
    exact sub_le_self (y ξ x 1) (eventually_pos_floor ξ x 1 (le_of_eq (refl 1))) },
end

lemma exists_limit : ∃ a, tendsto (λ n, y ξ x n) at_top (𝓝 a) :=
begin
  have h_bdd : bdd_below (range (shift_y ξ x)), sorry,
  have := tendsto_at_top_cinfi (eventually_monotone ξ x) h_bdd,
  use (⨅ (i : ℕ), shift_y ξ x i),
  apply @tendsto.congr' _ _ (shift_y ξ x) _ _ _ _ this,
  sorry,
end


lemma finite_sum (n : ℕ) : (y ξ x (n + 1) : ℝ) =
  x - ∑ i in range(n + 1),  (⌊(((y ξ x i) / ξ ^ i) : ℝ)⌋ : ℝ) * (ξ ^ i) :=
begin
  induction n with n h_ind,
  { rw [zero_add, range_one, sum_singleton],-- ← coe_pow, ← coe_mul, ← nnreal.coe_sub,
    -- nnreal.eq_iff],
   refl },
  { replace h_ind : (x - (y ξ x (n + 1)) : ℝ) =
    ∑ i in range(n + 1),  (⌊(y ξ x i / ξ ^ i : ℝ)⌋ : ℝ) * ξ ^ i := by {rw [sub_eq_iff_eq_add,
      ← sub_eq_iff_eq_add', h_ind] },
    nth_rewrite_rhs 2 [nat.succ_eq_add_one, ← nat.succ_eq_add_one, range_succ],
    rw [sum_insert, nat.succ_eq_add_one, ← sub_sub, ← h_ind, sub_sub, add_sub, add_comm _ x,
      ← add_sub, ← sub_sub, sub_self, zero_sub, neg_sub],
    refl,
    simp },
end

lemma geometric : --(ξ : ℝ) (h_pos : 0 < ξ) (h_small : ξ < 1) :
  summable (λ i, (⌊(y ξ x i / ξ ^ i : ℝ)⌋ : ℝ) * ξ ^ i) :=
begin
  sorry,--use cauchy_seq_of_le_geometric and its friends
end


lemma limit (h_pos : 0 < ξ) (h_small : ξ < 1)
  : tendsto (λ n, y ξ x n) at_top (𝓝 0) :=
begin
  have h_right : ∀ n, n ≥ 1 → (⌊(y ξ x n / ξ ^ n)⌋ : ℝ) ≤ (y ξ x n / ξ ^ n) := (λ _ _, floor_le _),
  replace h_right : ∀ n, n ≥ 1 → (⌊(y ξ x n / ξ ^ n)⌋ : ℝ) * ξ ^ n  ≤ y ξ x n :=
    (λ n hn, (le_div_iff (pow_pos h_pos n)).mp (h_right n hn)),
  replace h_right : ∀ᶠ n in at_top, (⌊(y ξ x n / ξ ^ n)⌋ : ℝ) * ξ ^ n  ≤ y ξ x n,
  { simp only [ge_iff_le, eventually_at_top], use [1, h_right] },
  have h_left : ∀ n, n ≥ 1 → (y ξ x n / ξ ^ n) - 1 ≤ ⌊(y ξ x n / ξ ^ n)⌋ :=
    (λ n hn, le_of_lt (sub_one_lt_floor _)),
  replace h_left : ∀ n, n ≥ 1 → (y ξ x n - ξ ^ n) ≤ ⌊(y ξ x n / ξ ^ n)⌋ * ξ ^ n,
  { have h_one : ∀ n : ℕ, 0 < ξ ^ n := (λ n, pow_pos h_pos n),
    intros n hn,
    calc y ξ x n -  ξ ^ n = (y ξ x n * ξ ^ n / ξ ^ n  - ξ ^ n) :
                                                by {rw [mul_div_cancel _ (ne_of_lt (h_one n)).symm]}
                    ... = (y ξ x n / ξ ^ n * ξ ^ n  - ξ ^ n) :
                                                  by {rw [mul_div_assoc, ← div_mul_eq_mul_div_comm]}
                    ... = ((y ξ x n / ξ ^ n) - 1 ) * ξ ^ n :
                                            by {nth_rewrite_lhs 2 [← one_mul (ξ ^ n)], rw ← sub_mul}
                    ... ≤ ⌊(y ξ x n / ξ ^ n)⌋ * ξ ^ n :
                                                  (mul_le_mul_right (h_one n)).mpr (h_left n hn) },
  replace h_left : ∀ᶠ n in at_top, y ξ x n - ξ ^ n ≤ (⌊(y ξ x n / ξ ^ n)⌋ : ℝ) * ξ ^ n,
  { simp only [eventually_at_top], use [1, h_left] },
  have : tendsto (λ n, y ξ x n - ξ ^ n) at_top (𝓝 (exists_limit ξ x).some), sorry,
  have exact := (le_of_tendsto_of_tendsto this (geometric ξ x).tendsto_at_top_zero h_left).antisymm
   (le_of_tendsto_of_tendsto (geometric ξ x).tendsto_at_top_zero (exists_limit ξ x).some_spec
    h_right),
  have := (exists_limit ξ x).some_spec,
  rwa exact at this,
end



end fae_surjectivity
