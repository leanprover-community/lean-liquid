import category_theory.Fintype
import data.real.nnreal
import laurent_measures.basic
import order.filter.at_top_bot
import analysis.special_functions.exp_log

noncomputable theory

open real (log)

open_locale nnreal

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

def step (m : ℕ) (L : ℤ) : ℕ × ℝ≥0 := (a y (L + m), z y (L + m))

noncomputable def A : ℕ → ℕ × ℝ≥0
| 0         := step y 0 (deg y)
| (m + 1)   := step (A m).2 (m + 1) (deg y)--let z' := (A m).2, c := n y + m + 1 in (a z' c, z z' c)

lemma deg_increasing (k : ℕ) : deg (A y (k + 1)).2 > deg (A y k).2 := sorry

def coeff : ℤ → ℕ := λ k, if k < deg y then 0 else (A y (k + deg y ).to_nat).1

lemma surj_on_nonneg : has_sum (λ k : ℤ, (coeff y k : ℝ≥0) * x ^ k ) y := sorry







end surjectivity
end thm71
