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

parameters (ξ : ℝ) (h_pos : 0 < ξ) (h_small : ξ < 1)
variable (x : ℝ)

noncomputable def y : ℕ → ℝ
| 0         := x
| (n + 1)   := (y n) - (⌊(((y n) / ξ ^ n) : ℝ)⌋ : ℝ) * ξ ^ n

lemma finite_sum (n : ℕ) : (y x (n + 1) : ℝ) =
  x - ∑ i in range(n + 1),  (⌊(((y x i) / ξ ^ i) : ℝ)⌋ : ℝ) * (ξ ^ i) :=
begin
  induction n with n h_ind,
  { rw [zero_add, range_one, sum_singleton],-- ← coe_pow, ← coe_mul, ← nnreal.coe_sub,
    -- nnreal.eq_iff],
   refl },
  { replace h_ind : (x - (y x (n + 1)) : ℝ) =
    ∑ i in range(n + 1),  (⌊(y x i / ξ ^ i : ℝ)⌋ : ℝ) * ξ ^ i := by {rw [sub_eq_iff_eq_add,
      ← sub_eq_iff_eq_add', h_ind] },
    nth_rewrite_rhs 2 [nat.succ_eq_add_one, ← nat.succ_eq_add_one, range_succ],
    rw [sum_insert, nat.succ_eq_add_one, ← sub_sub, ← h_ind, sub_sub, add_sub, add_comm _ x,
      ← add_sub, ← sub_sub, sub_self, zero_sub, neg_sub],
    refl,
    simp },
end


lemma limit (ξ : ℝ) (h_pos : 0 < ξ) (h_small : ξ < 1) : tendsto (λ n, y x n) at_top (𝓝 0) :=
begin
  have h_lt : ∀ n, n ≥ 1 → (y x n / ξ ^ n) - 1 < ⌊(y x n / ξ ^ n)⌋ := (λ n hn, sub_one_lt_floor _),
  have h_le : ∀ n, n ≥ 1 → (⌊(y x n / ξ ^ n)⌋ : ℝ) ≤ (y x n / ξ ^ n) := (λ n hn, floor_le _),
  replace h_lt : ∀ n, n ≥ 1 → (y x n - ξ ^ n) < ⌊(y x n / ξ ^ n)⌋ * ξ ^ n,
  have h_one : ∀ n : ℕ, 0 < ξ ^ n := (λ n, pow_pos h_pos n),
  intros n hn,
  calc y x n -  ξ ^ n = (y x n * ξ ^ n / ξ ^ n  - ξ ^ n) : by {rw [mul_div_cancel _ (ne_of_lt (h_one n)).symm]}
                  ... = (y x n / ξ ^ n * ξ ^ n  - ξ ^ n) : by {rw [mul_div_assoc, ← div_mul_eq_mul_div_comm]}
                  ... = ((y x n / ξ ^ n) - 1 ) * ξ ^ n : by {nth_rewrite_lhs 2 [← one_mul (ξ ^ n)], rw ← sub_mul}
                  ... < ⌊(y x n / ξ ^ n)⌋ * ξ ^ n : (mul_lt_mul_right (h_one n)).mpr (h_lt n hn),
  sorry,



end



end fae_surjectivity
