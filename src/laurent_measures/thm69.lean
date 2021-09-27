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

variables (ξ : ℝ)-- [h_pos : 0 < ξ] [h_small : ξ < 1]
variable (x : ℝ)

noncomputable def y : ℕ → ℝ
| 0         := x
| (n + 1)   := (y n) - (⌊(((y n) / ξ ^ n) : ℝ)⌋ : ℝ) * ξ ^ n

example (f : ℕ → ℝ) (h_mono : monotone f) :
  tendsto f at_top at_top ∨ (∃ l, tendsto f at_top (𝓝 l)) := tendsto_of_monotone h_mono

lemma eventually_monotone : monotone (λ n : ℕ, y ξ x n.succ) :=
begin
  sorry,
end

lemma exists_limit : ∃ a, tendsto (λ n, y ξ x n) at_top (𝓝 a) := sorry--use the above and that for two
-- functions which are eventually equal, one admits a limit iff the other does


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
