import normed_spectral -- some constants are defined in this file, might want to move them
import polyhedral_lattice.category

/-!
# Explicit formulas for the constants in theorem 9.5
-/

noncomputable theory

open_locale nnreal

variables (c' : ℕ → ℝ≥0)
-- variables (BD : breen_deligne.package) [BD.suitable c']
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : NormedGroup) [normed_with_aut r V]
variables (Λ : PolyhedralLattice) -- (M : ProFiltPseuNormGrpWithTinv r')
variables (m : ℕ)

namespace thm95

namespace universal_constants

open system_of_double_complexes

def k : ℕ → ℝ≥0
| 0     := 2 -- should be anything > 1
| (m+1) := sorry

def K : ℕ → ℝ≥0
| 0     := 2 -- should be anything > 1, probably
| (m+1) := sorry

/-- `k₀ m` is the constant `k₀ m (k m)` used in the proof of `normed_spectral` -/
def k₀ : ℝ≥0 := normed_spectral.k₀ m (k m)

/-- `K₀ m` is the constant `K₀ m (K m)` used in the proof of `normed_spectral` -/
def K₀ : ℝ≥0 := normed_spectral.K₀ m (K m)

/-- `ε m` is the constant `ε m (K m)` used in the proof of `normed_spectral` -/
def ε : ℝ≥0 := normed_spectral.ε m (K m)

/-- `k' c' m` is the maximum of `k₀ m` and the constants `c' 0`, `c' 1`, ..., `c' m` -/
def k' : ℝ≥0 := max (k₀ m) $ (finset.range (m+1)).sup c'

-- in the PDF `b` is *positive*, we might need to make that explicit
lemma b_exists : ∃ b : ℕ, 2 * (k' c' m) * (r / r') ^ b ≤ (ε m) :=
sorry

/-- `b c' r r' m` is the smallest `b` such that `2 * (k' c' m) * (r / r') ^ b ≤ (ε m)` -/
def b : ℕ := nat.find (b_exists c' r r' m)

lemma N₂_exists : ∃ N₂ : ℕ, (k' c' m) / (2 ^ N₂) ≤ r' ^ (b c' r r' m) :=
sorry

/-- `N₂ c' r r' m` is the smallest `N₂` such that `N = 2 ^ N₂` satisfies
`(k' c' m) / N ≤ r' ^ (b c' r r' m)` -/
def N₂ : ℕ := nat.find (N₂_exists c' r r' m)

lemma r_pow_b_mul_two_pow_N₂_le :
  r ^ (b c' r r' m) * (2 ^ N₂ c' r r' m) ≤ (2 / k' c' m) * (r / r') ^ (b c' r r' m) :=
sorry

lemma two_div_k'_mul_r_div_r'_pow_b_le :
  (2 / k' c' m) * (r / r') ^ (b c' r r' m) ≤ ε m :=
sorry


end universal_constants

end thm95
