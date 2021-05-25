import data.real.sqrt
import analysis.special_functions.pow

import polyhedral_lattice.cosimplicial
import combinatorial_lemma
import breen_deligne.eg

import facts.nnreal
/-!
# Explicit formulas for the constants in theorem 9.5
-/

noncomputable theory

open_locale nnreal


open real

lemma real.log_pow {x : ℝ} (hx : 0 < x) (n : ℕ) : real.log (x ^ n) = n * real.log x :=
begin
  suffices : real.log (x ^ (n : ℝ)) = n * real.log x,
  convert this using 2,
  simp,
  rw log_rpow hx
end

namespace helper

open real

def b (r r' k' ε : ℝ): ℕ := nat_ceil ((log $ ε/(2 * k'))/log (r/r'))

lemma b_spec {r r' k' ε : ℝ} (hr : 0 < r) ( hr' : 0 < r') (hrr' : r < r')
  (hk' : 0 < k') (hε : 0 < ε) : (2 * k') * (r / r') ^ (b r r' k' ε) ≤ ε :=
begin
  have f₁ : 0 < 2*k' := mul_pos zero_lt_two hk',
  have f₂ : r/r' < 1 := (div_lt_one hr').mpr hrr',
  have f₃ : 0 < r/r' := div_pos hr hr',
  have f₄ :0 < (r / r') ^ b r r' k' ε := pow_pos f₃ _,
  rw [← le_div_iff' f₁, ← log_le_log f₄ (div_pos hε f₁), log_pow f₃, ← div_le_iff_of_neg (log_neg f₃ f₂)],
  exact le_nat_ceil (log (ε / (2 * k')) / log (r / r')),
end

def N₂ (r' k' b : ℝ) := nat_ceil (log (k'/r'^b)/ log 2)

lemma N₂_spec {r' k' b : ℝ} (hr' : 0 < r') (hk' : 0 < k') : k'/ (2 ^ (N₂ r' k' b)) ≤ r' ^ b :=
begin
  have f₁ : (0 : ℝ) < 2 ^ N₂ r' k' b := pow_pos zero_lt_two _,
  have f₂ : (0 : ℝ) < r' ^ b := rpow_pos_of_pos hr' _,
  have f₃ : 0 < k' / r' ^ b := div_pos hk' f₂,
  have f₄ : 0 < log 2 := log_pos one_lt_two,
  rw [div_le_iff' f₁, ← div_le_iff f₂,  ← log_le_log f₃ f₁, log_pow zero_lt_two, ← div_le_iff f₄],
  apply le_nat_ceil,
end

end helper

variables (BD : breen_deligne.package) (c_ c' : ℕ → ℝ≥0)
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables [breen_deligne.package.adept BD c_ c'] [BD.data.very_suitable r r' c_]
variables (Λ : PolyhedralLattice)
variables (m : ℕ)

namespace system_of_double_complexes
namespace normed_spectral

noncomputable
def ε : Π (m : ℕ) (K : ℝ≥0), ℝ≥0
| 0     K := (2 * K)⁻¹
| (m+1) K := ε m (K * (K * K + 1))

lemma ε_pos : ∀ m K [fact (1 ≤ K)], 0 < ε m K
| 0     K hK := nnreal.inv_pos.mpr (mul_pos zero_lt_two (lt_of_lt_of_le zero_lt_one hK.out))
| (m+1) K hK := by { dsimp [ε], exactI ε_pos m _ }

--noncomputable
def k₀ : Π (m : ℕ) (k : ℝ≥0), ℝ≥0
| 0     k := k
| (m+1) k := k₀ m (k * k * k)

instance one_le_k₀ : ∀ m k [fact (1 ≤ k)], fact (1 ≤ k₀ m k)
| 0     k hk := hk
| (m+1) k hk := by { dsimp [k₀], exactI one_le_k₀ m _ }

noncomputable
def K₀ : Π (m : ℕ) (K : ℝ≥0), ℝ≥0
| 0     K := K
| (m+1) K := K₀ m (K * (K * K + 1))

instance one_le_K₀ : ∀ m K [fact (1 ≤ K)], fact (1 ≤ K₀ m K)
| 0     K hK := hK
| (m+1) K hK := by { dsimp [K₀], exactI one_le_K₀ m _ }

end normed_spectral
end system_of_double_complexes
