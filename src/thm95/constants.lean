import polyhedral_lattice.category
import breen_deligne.suitable

import facts.nnreal

/-!
# Explicit formulas for the constants in theorem 9.5
-/

noncomputable theory

open_locale nnreal

variables (BD : breen_deligne.package) (c_ c' : ℕ → ℝ≥0)
variables [BD.data.suitable c_] [breen_deligne.package.adept BD c_ c']
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]
variables (V : NormedGroup)
variables (Λ : PolyhedralLattice) -- (M : ProFiltPseuNormGrpWithTinv r')
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

noncomputable
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

namespace thm95

namespace universal_constants

open system_of_double_complexes

-- this should be a constant roughly determined by `combinatorial_lemma.lean` (`lem98`)
-- it should probably also depend on an `N : ℕ`
def c₀ (Λ : PolyhedralLattice) : ℝ≥0 :=
sorry

def k₁ : ℕ → ℝ≥0
| 0     := 2 -- should be anything > 1
| (m+1) := sorry

instance one_le_k₁ : ∀ m, fact (1 ≤ k₁ m)
| 0     := ⟨one_le_two⟩
| (m+1) := sorry

def K₁ : ℕ → ℝ≥0
| 0     := 2 -- should be anything > 1, probably
| (m+1) := sorry

instance one_le_K₁ : ∀ m, fact (1 ≤ K₁ m)
| 0     := ⟨one_le_two⟩
| (m+1) := sorry

-- === jmc: I'm not completely convinced that the next three abbreviations are correct
-- === maybe we should pass an `m-1` around somewhere...

/-- `k₀ m` is the constant `k₀ m (k m)` used in the proof of `normed_spectral` -/
abbreviation k₀ : ℝ≥0 := normed_spectral.k₀ m (k₁ m)

/-- `K₀ m` is the constant `K₀ m (K m)` used in the proof of `normed_spectral` -/
abbreviation K₀ : ℝ≥0 := normed_spectral.K₀ m (K₁ m)

/-- `ε m` is the constant `ε m (K m)` used in the proof of `normed_spectral` -/
abbreviation ε : ℝ≥0 := normed_spectral.ε m (K₁ m)

instance ε_pos : fact (0 < ε m) := ⟨normed_spectral.ε_pos _ _⟩

/-- `k' c' m` is the maximum of `k₀ m` and the constants `c' 0`, `c' 1`, ..., `c' m` -/
def k' : ℝ≥0 := max (k₀ m) $ (finset.range (m+1)).sup c'

instance one_le_k' : fact (1 ≤ k' c_ m) :=
⟨le_trans (fact.out _) $ le_max_left _ _⟩

instance k₀_le_k' : fact (normed_spectral.k₀ m (k₁ m) ≤ k' c_ m) := ⟨le_max_left _ _⟩

-- in the PDF `b` is *positive*, we might need to make that explicit
lemma b_exists : ∃ b : ℕ, 2 * (k' c_ m) * (r / r') ^ b ≤ (ε m) :=
begin
  have : 0 < 2 * (k' c_ m) := mul_pos zero_lt_two (fact.out _),
  simp only [nnreal.mul_le_iff_le_inv this.ne'],
  have h₁ : 0 < ((2 * k' c_ m)⁻¹ * ε m : ℝ),
  { refine mul_pos (inv_pos.mpr this) _,
    rw [nnreal.coe_pos],
    exact fact.out _ },
  have h₂ : (r / r' : ℝ) < 1,
  { rw div_lt_iff,
    { rw [one_mul, nnreal.coe_lt_coe], exact fact.out _ },
    { rw [nnreal.coe_pos], exact fact.out _ } },
  obtain ⟨b, hb⟩ := exists_pow_lt_of_lt_one h₁ h₂,
  use b,
  exact_mod_cast hb.le,
end

/-- `b c_ r r' m` is the smallest `b` such that `2 * (k' c_ m) * (r / r') ^ b ≤ (ε m)` -/
def b : ℕ := nat.find (b_exists c_ r r' m)

lemma N₂_exists : ∃ N₂ : ℕ, (k' c_ m) / (2 ^ N₂) ≤ r' ^ (b c_ r r' m) :=
begin
  suffices : ∃ N₂ : ℕ, ((2⁻¹ : ℝ≥0) ^ N₂ : ℝ) < (k' c_ m)⁻¹ * r' ^ (b c_ r r' m),
  { rcases this with ⟨N₂, h⟩,
    use N₂,
    rw [← div_lt_iff', ← nnreal.coe_pow, inv_pow', nnreal.coe_inv, inv_div_left, mul_inv',
      inv_inv', ← div_eq_mul_inv] at h,
    { exact_mod_cast h.le },
    { rw [inv_pos, nnreal.coe_pos], exact fact.out _ } },
  refine exists_pow_lt_of_lt_one (mul_pos _ _) _,
  { rw [inv_pos, nnreal.coe_pos], exact fact.out _ },
  { apply pow_pos, rw [nnreal.coe_pos], exact fact.out _ },
  { norm_num }
end

/-- `N₂ c_ r r' m` is the smallest `N₂` such that `N = 2 ^ N₂` satisfies
`(k' c_ m) / N ≤ r' ^ (b c_ r r' m)` -/
def N₂ : ℕ := nat.find (N₂_exists c_ r r' m)

/-- `N c_ r r' m = 2 ^ N₂ c_ r r' m` is the smallest `N` that satisfies
`(k' c_ m) / N ≤ r' ^ (b c_ r r' m)` -/
def N : ℕ := 2 ^ N₂ c_ r r' m

instance N_pos : fact (0 < N c_ r r' m) := ⟨pow_pos zero_lt_two _⟩

lemma r_pow_b_mul_N_le :
  r ^ (b c_ r r' m) * (N c_ r r' m) ≤ (2 / k' c_ m) * (r / r') ^ (b c_ r r' m) :=
sorry

lemma two_div_k'_mul_r_div_r'_pow_b_le :
  (2 / k' c_ m) * (r / r') ^ (b c_ r r' m) ≤ ε m :=
sorry

include BD c_ r r' m

/-- `H BD c_ r r' m` is the universal bound on the norm of the `N₂`th Breen--Deligne homotopy
in the first `m` degrees. Here `N₂ = thm95.N₂ c_ r r' m`. -/
def H : ℝ≥0 :=
sorry

omit BD c_ r r' m

instance H_pos : fact (0 < H BD c_ r r' m) := sorry

def k : ℝ≥0 := k' c_ m * k' c_ m

instance one_le_k : fact (1 ≤ k c_ m) := by { delta k, apply_instance }

def K : ℝ≥0 := 2 * normed_spectral.K₀ m (K₁ m) * H BD c_ r r' m

instance one_le_K : fact (1 ≤ K BD c_ r r' m) := sorry

instance k_le_k₁ : fact (k c_ (m - 1) ≤ k₁ m) := sorry

instance K_le_K₁ : fact (K BD c_ r r' (m - 1) ≤ K₁ m) := sorry

end universal_constants

end thm95
