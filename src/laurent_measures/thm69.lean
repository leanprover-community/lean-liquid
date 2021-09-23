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

def n : ℤ := ⌊(log y) / (log x)⌋

lemma xpow_le : x ^ (n y) ≤ y := sorry

lemma n_is_min : ∀ k < n, x ^ (n y) > y := sorry

def a (m : ℤ) := ⌊ (y / x ^ m : ℝ)⌋₊

lemma a_bdd : a y (n y) < N  := sorry

lemma y_mul_xpow_le : ((a y (n y) : ℝ≥0) * x ^ (n y)) ≤ y := sorry

def z (m : ℤ) := y - (a y m) * x ^ m

def A : ℕ → ℕ × ℝ≥0
| 0         := (a y (n y), z y (n y))
| (m + 1)   := let z' := (A m).2, c := n y + m + 1 in (a z' c, z z' c)








end surjectivity
end thm71
