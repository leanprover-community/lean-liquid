import facts.nnreal

/-!
# Explicit formulas for the constants used in Proposition 9.6 of Analytic.pdf
-/

open_locale nnreal

namespace system_of_double_complexes
namespace normed_spectral

/-- `ε m K` is a sequence of nonnegative real constants,
depending on a natural number `m` and a nonnegative real number `K`.
It is defined recursively, via `ε 0 K = (2 * K)⁻¹` and `ε (m+1) K = ε m (K^3 + K)`. -/
noncomputable def ε : Π (m : ℕ) (K : ℝ≥0), ℝ≥0
| 0     K := (2 * K)⁻¹
| (m+1) K := ε m (K * (K * K + 1))

/-- The number `ε m K` is always positive. -/
lemma ε_pos : ∀ m K [fact (0 < K)], 0 < ε m K
| 0     K hK := nnreal.inv_pos.mpr (mul_pos zero_lt_two hK.out)
| (m+1) K hK := by { dsimp [ε], exactI ε_pos m _ }

/-- `k₀ m k` is a sequence of nonnegative real constants,
depending on a natural number `m` and a nonnegative real number `k`.
It is defined recursively, via `k₀ 0 k = k` and `k₀ (m+1) k = k₀ m (k^3)`. -/
def k₀ : Π (m : ℕ) (k : ℝ≥0), ℝ≥0
| 0     k := k
| (m+1) k := k₀ m (k * k * k)

/-- We have `1 ≤ k₀ m k` whenever `1 ≤ k` holds. -/
instance one_le_k₀ : ∀ m k [fact (1 ≤ k)], fact (1 ≤ k₀ m k)
| 0     k hk := hk
| (m+1) k hk := by { dsimp [k₀], exactI one_le_k₀ m _ }

/-- `K₀ m k` is a sequence of nonnegative real constants,
depending on a natural number `m` and a nonnegative real number `K`.
It is defined recursively, via `K₀ 0 K = K` and `K₀ (m+1) K = K₀ m (K^3 + K)`. -/
def K₀ : Π (m : ℕ) (K : ℝ≥0), ℝ≥0
| 0     K := K
| (m+1) K := K₀ m (K * (K * K + 1))

/-- We have `1 ≤ K₀ m K` whenever `1 ≤ K` holds. -/
instance one_le_K₀ : ∀ m K [fact (1 ≤ K)], fact (1 ≤ K₀ m K)
| 0     K hK := hK
| (m+1) K hK := by { dsimp [K₀], exactI one_le_K₀ m _ }

end normed_spectral
end system_of_double_complexes
