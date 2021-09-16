import analysis.special_functions.pow

import combinatorial_lemma
import breen_deligne.eg

import thm95.constants.spectral_constants

import for_mathlib.nnreal
/-!
# Explicit formulas for the constants in theorem 9.5
-/

noncomputable theory

open_locale nnreal


open real finset

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

lemma N₂_spec_of_pos' {r' k' b} (h : 0 < N₂ r' k' b) (hr' : 0 < r') (hk' : 0 ≤ k') :
  r' ^ b < 2 * k'  / 2 ^ N₂ r' k' b :=
begin
  have h' := lt_nat_ceil.mp h,
  have : 0 < log (k'/r'^b)/ log 2,
  { exact_mod_cast lt_nat_ceil.mp h },
  have f₁ : 0 < 2 ^ N₂ r' k' b := pow_pos zero_lt_two _,
  have Hk' : k' ≠ 0,
  { intro H,
    simpa [H, N₂] using h },
  have f₂ : 0 < r' ^ b := rpow_pos_of_pos hr' b,

  have f₃ : 0 < k' / r' ^ b := div_pos ((ne.symm Hk').le_iff_lt.mp hk') f₂,
  have f₃' : k' / r' ^ b ≠ 0 := f₃.ne.symm,
  have f₄ : (N₂ r' k' b : ℝ) < _ := nat_ceil_lt_add_one this.le,

  rwa [lt_div_iff, ← lt_div_iff', mul_div_assoc, ← log_lt_log_iff, log_mul, log_pow,
       ← lt_div_iff (log_pos one_lt_two), add_div, div_self (log_pos one_lt_two).ne.symm, add_comm],
  all_goals { assumption <|> norm_num  },
  assumption
end

end helper

section

parameters (r r' : ℝ≥0)
parameters (BD : breen_deligne.package) (κ κ' : ℕ → ℝ≥0)
parameters [breen_deligne.package.adept BD κ κ'] [BD.data.very_suitable r r' κ]
parameters (Λ : PolyhedralLattice)
variables  (m : ℕ)

namespace thm95

open system_of_double_complexes

namespace universal_constants

open breen_deligne

noncomputable
def k₁ : ℕ → ℝ≥0
| 0     := 2 -- should be anything > 1
| (m+1) := max 2 ((max (normed_spectral.k₀ m (k₁ m)) $ (range $ m+2).sup κ')^2)

instance one_lt_k₁ : Π (m : ℕ), fact (1 < k₁ m)
| 0     := ⟨one_lt_two⟩
| (m+1) := ⟨lt_of_lt_of_le one_lt_two (le_max_left _ _)⟩

instance one_le_k₁ (m : ℕ) : fact (1 ≤ k₁ m) := ⟨(fact.out (1 < k₁ m)).le⟩

/-- `k₀ m` is the constant `k₀ m (k m)` used in the proof of `normed_spectral` -/
abbreviation k₀ : ℝ≥0 := normed_spectral.k₀ m (k₁ m)

/-- `k' m` is the maximum of `k₀ m` and the constants `κ' 0`, `κ' 1`, ..., `κ' m`, `κ' (m+1)` -/
def k' : ℝ≥0 := max (k₀ m) $ (range $ m+2).sup κ'

lemma κ'_le_k' {i : ℕ} (hi : i ≤ m+1) : κ' i ≤ k' m :=
le_max_iff.mpr $ or.inr $ le_sup $ mem_range.mpr $ nat.lt_succ_iff.mpr hi

instance fact_κ'_le_k' {i : ℕ} (hi : fact (i ≤ m+1)) : fact (κ' i ≤ k' m) :=
⟨κ'_le_k' _ hi.1⟩

instance one_le_k' : fact (1 ≤ k' m) :=
⟨le_trans (fact.out _) $ le_max_left _ _⟩

instance k₀_le_k' : fact (normed_spectral.k₀ m (k₁ m) ≤ k' m) := ⟨le_max_left _ _⟩

def k : ℝ≥0 := k' m * k' m

instance one_le_k : fact (1 ≤ k m) := by { delta k, apply_instance }

instance k_le_k₁ [fact (0 < m)] : fact (k (m - 1) ≤ k₁ m) :=
begin
  unfreezingI {cases m},
  { exact false.elim (lt_irrefl 0 (fact.elim infer_instance)) },
  { apply fact.mk,
    simp only [k₁],
    convert le_max_right _ _,
    rw pow_two,
    refl }
end

def k₁_sqrt : ℝ≥0 := ⟨real.sqrt (k₁ m), real.sqrt_nonneg _⟩

instance one_lt_k₁_sqrt : fact (1 < k₁_sqrt m) := ⟨begin
  change (1 : ℝ) < real.sqrt (k₁ κ' m),
  rw [real.lt_sqrt zero_le_one, pow_two, mul_one],
  exact (universal_constants.one_lt_k₁ κ' m).elim,
  exact (k₁ κ' m).coe_nonneg,
end⟩

def y (m : ℕ) (r : ℝ≥0):= (m + 2 : ℝ≥0) + (r + 1) / (r * (1 - r)) * (m + 2)^2

def H' (n : ℕ) :=
max 1 ((range $ m+1).sup $ λ q, ((BD.data.homotopy_mul BD.homotopy n).hom q (q + 1)).bound)

noncomputable
def K₁ : ℕ → ℝ≥0
| 0     := 2 + (r + 1) / (r * (1 - r)) * 4
| (m+1) :=
max (y (m+1) r)
    (2 * normed_spectral.K₀ m (K₁ m) *
         (H' m $ helper.N₂ r' (k' m) (helper.b r r' (k' m) (normed_spectral.ε m (K₁ m)))))

instance one_le_K₁ : ∀ m, fact (1 ≤ K₁ m)
| 0     := ⟨begin
             dsimp [K₁],
             apply le_add_right,
             exact one_le_two
            end⟩
| (m+1) := ⟨begin
              dsimp [K₁],
              refine le_max_iff.mpr (or.inl _),
              dsimp [y],
              apply le_add_right,
              norm_cast,
              exact le_add_self
            end⟩

/-- `K₀ m` is the constant `K₀ m (K m)` used in the proof of `normed_spectral` -/
abbreviation K₀ : ℝ≥0 := normed_spectral.K₀ m (K₁ m)

/-- `ε m` is the constant `ε m (K m)` used in the proof of `normed_spectral` -/
abbreviation ε : ℝ≥0 := normed_spectral.ε m (K₁ m)

instance ε_pos : fact (0 < ε m) := ⟨normed_spectral.ε_pos _ _⟩

variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)]

-- in the PDF `b` is *positive*, we might need to make that explicit

/-- `b κ' r r' m` is the smallest `b` such that `2 * (k' m) * (r / r') ^ b ≤ (ε m)` -/
def b : ℕ := helper.b r r' (k' m) (ε m)

lemma b_spec :
  (2 * k' m) * (r / r') ^ (b m) ≤ ε m :=
begin
  suffices : 2 * (k' κ' m : ℝ) * (r / r') ^ b r r' BD κ' m ≤ ε r r' BD κ' m,
  exact_mod_cast this,
  apply helper.b_spec ; norm_cast ; apply fact.out,
end

/-- `N₂ κ' r r' m` is the smallest `N₂` such that `N = 2 ^ N₂` satisfies
`(k' m) / N ≤ r' ^ (b κ' r r' m)` -/
def N₂ : ℕ := helper.N₂ r' (k' m) (b m)

lemma N₂_spec : (k' m) / (2 ^ (N₂ m)) ≤ r' ^ b m :=
begin
  suffices : (k' κ' m : ℝ) / 2 ^ N₂ r r' BD κ' m ≤ r' ^ (b r r' BD κ' m : ℝ),
  exact_mod_cast this,
  apply helper.N₂_spec ; norm_cast ; apply fact.out
end

lemma N₂_spec_of_pos' (h : 0 < N₂ m) :
  r' ^ b m < 2 * k' m / 2 ^ N₂ m :=
begin
  suffices : (r' : ℝ) ^ (b r r' BD κ' m : ℝ) < 2 * k' κ' m / 2 ^ N₂ r r' BD κ' m,
  exact_mod_cast this,
  apply helper.N₂_spec_of_pos' h,
  { norm_cast,
    apply fact.out },
  apply nnreal.coe_nonneg
end

lemma k'_eq_one_of_N₂_spec_eq_zero (h : N₂ m = 0) :
  k' m = 1 :=
begin
  refine le_antisymm _ (universal_constants.one_le_k' _ _).1,
  obtain F := N₂_spec r r' BD κ' m,
  rw [h, pow_zero, div_one] at F,
  refine F.trans (pow_le_one (b r r' BD κ' m) (le_of_lt _) _);
  { apply fact.out _,
    assumption }
end

/-- `N m = 2 ^ N₂ m` is the smallest `N` that satisfies `(k' m) / N ≤ r' ^ (b m)` -/
def N : ℕ := 2 ^ N₂ m

instance N_pos : fact (0 < N m) := ⟨pow_pos zero_lt_two _⟩

instance k'_le_two_pow_N : fact (k' m ≤ 2 ^ N₂ m) :=
{ out := begin
  rw [← mul_one ((2 : ℝ≥0) ^ _)],
  obtain F := N₂_spec r r' BD κ' m,
  rw [nnreal.div_le_iff (pow_pos zero_lt_two _).ne', mul_comm] at F,
  refine F.trans (mul_le_mul rfl.le _ _ _),
  { refine pow_le_one _ (zero_le r') _,
    apply fact.out _,
    assumption },
  repeat { exact pow_nonneg (zero_le _) _ }
end }

lemma r_pow_b_mul_N_le : r ^ (b m) * (N m) ≤ 2 * k' m * (r / r') ^ (b m) :=
begin
  rw [mul_comm _ (_ ^ _), N, div_pow, nat.cast_pow, nat.cast_bit0, nat.cast_one, div_eq_mul_one_div,
    mul_assoc, div_mul_comm', mul_one],
  refine mul_le_mul_left' _ _,
  rw [nnreal.le_div_iff_mul_le, mul_comm, ← nnreal.le_div_iff_mul_le],
  { by_cases N0 : N₂ r r' BD κ' m = 0,
    { rw [k'_eq_one_of_N₂_spec_eq_zero _ _ BD _ _ N0, mul_one, N0, pow_zero, div_one],
      refine le_trans (pow_le_one _ (nnreal.coe_nonneg _) _) one_le_two,
      apply fact.out _,
      assumption },
    { exact le_of_lt (N₂_spec_of_pos' _ _ BD _ _ (zero_lt_iff.mpr N0)) } },
  { exact pow_ne_zero _ two_ne_zero },
  { exact pow_ne_zero _ (ne_of_gt (fact.out _)) }
end

lemma r_pow_b_le_ε : r ^ b m * N m ≤ ε m := (r_pow_b_mul_N_le _).trans (b_spec _)

lemma N₂_speκ' : k' m * (2 ^ N₂ m)⁻¹ ≤ r' ^ b m :=
by { rw [inv_eq_one_div, mul_one_div], exact N₂_spec r r' BD κ' m }

/-- `H BD κ r r' m` is the universal bound on the norm of the `N₂`th Breen--Deligne homotopy
in the first `m` degrees. Here `N₂ = thm95.N₂ κ' r r' m`. -/
def H : ℕ := H' m (N₂ m)

lemma one_le_H : 1 ≤ H m := le_max_left _ _

instance H_pos : fact (0 < H m) := ⟨zero_lt_one.trans_le $ one_le_H _⟩

instance H_pos' : fact ((0:ℝ≥0) < H m) := by { norm_cast, apply_instance }

lemma bound_by_H {q : ℕ} (h : q ≤ m) :
  ((BD.data.homotopy_mul BD.homotopy (N₂ m)).hom q (q + 1)).bound_by (H m) :=
begin
  rw [H, H', universal_map.bound_by, le_max_iff],
  right,
  refine @le_sup _ _ _ (range $ m+1)
    (λ q, ((BD.data.homotopy_mul BD.homotopy (N₂ r r' BD κ' m)).hom q (q + 1)).bound) _ _,
  rwa [mem_range, nat.lt_succ_iff],
end


def K : ℝ≥0 := 2 * normed_spectral.K₀ m (K₁ m) * H m

instance one_le_K : fact (1 ≤ K m) := fact.mk $
calc 1 = 1 * 1 * 1 : by simp
... ≤ 2 * normed_spectral.K₀ m (K₁ m) * H m :
begin
  refine mul_le_mul' (mul_le_mul' one_le_two $ (normed_spectral.one_le_K₀ _ _).1) _,
  norm_cast,
  apply one_le_H
end

instance K_le_K₁ [fact (0 < m)] : fact (K (m - 1) ≤ K₁ m) :=
⟨begin
  tactic.unfreeze_local_instances,
  have hm : 0 < m, from fact.out _,
  cases m,
  { exfalso, exact nat.lt_asymm hm hm, },
  simp only [K₁, nat.succ_sub_succ_eq_sub, nat.sub_zero, le_max_iff],
  right,
  apply le_refl
end⟩

lemma K₁_spec : (m + 2 + (r + 1) / (r * (1 - r)) * (m + 2)^2 : ℝ≥0) ≤ K₁ m :=
begin
  cases m,
  { norm_num [K₁] },
  { simp only [K₁, le_max_iff],
    left,
    apply le_refl }
end

section open simplex_category

def c₀_aux (m : ℕ) (Λ : PolyhedralLattice) : ℝ≥0 :=
N m * lem98.d Λ (N m) / (k₁_sqrt m - 1) / r' / (range $ m+1).inf' ⟨0, by simp⟩ κ

-- define this such that the lemmas below hold
noncomputable def c₀ : ℕ → PolyhedralLattice → ℝ≥0
| 0 Λ := c₀_aux 0 Λ
| (m+1) Λ := max (c₀_aux (m+1) Λ)
    (max (c₀ m Λ)
    (max (c₀ m ((Λ.cosimplicial (N (m+1))).obj (mk 0)))
      ((range (m+1)).sup (λ i, c₀ m ((Λ.cosimplicial (N (m+1))).obj (mk (i + 1)))))))

-- Should we be unhappy that these lemmas have `fact` in them?
-- Putting aside the fact that we're badly abusing the `fact` system,
-- typeclass inference can even use these, because it can't provide the inequality arguments.

lemma c₀_mono : fact (c₀ (m - 1) Λ ≤ c₀ m Λ) :=
begin
  fsplit,
  cases m,
  { apply le_refl, },
  { dsimp [c₀],
    apply le_trans _ (le_max_right _ _),
    apply le_trans _ (le_max_left _ _),
    simp, }
end

lemma c₀_pred_le (hm : 0 < m) : fact (c₀ (m - 1) ((Λ.cosimplicial (N m)).obj (mk 0)) ≤  c₀ m Λ) :=
begin
  fsplit,
  cases m,
  { cases hm, },
  { dsimp [c₀],
    apply le_trans _ (le_max_right _ _),
    apply le_trans _ (le_max_right _ _),
    apply le_trans _ (le_max_left _ _),
    simp, }
end

lemma c₀_pred_le_of_le (i : ℕ) (hi : i + 2 ≤ m + 1) :
  fact (c₀ (m - 1) ((Λ.cosimplicial (N m)).obj (mk (i + 1))) ≤ c₀ m Λ) :=
begin
  fsplit,
  cases m,
  { simpa using nat.succ_le_succ_iff.mp hi, },
  { dsimp [c₀],
    replace hi : i ∈ range (m + 1) :=
      mem_range.mpr (nat.succ_le_iff.mp (nat.succ_le_succ_iff.mp hi)),
    apply le_trans _ (le_max_right _ _),
    apply le_trans _ (le_max_right _ _),
    apply le_trans _ (le_max_right _ _),
    simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero, nat.succ_eq_add_one],
    exact le_sup hi, }
end

lemma c₀_spec (j : ℕ) (hj : j ≤ m) :
  lem98.d Λ (N m) ≤ (k₁_sqrt m - 1) * (r' * (κ j * c₀ m Λ)) / (N m) :=
begin
  have w := BD.data.pos κ,
  -- TODO golf
  rw nnreal.le_div_iff',
  rw ←nnreal.div_le_iff',
  rw ←nnreal.div_le_iff',
  rw ←nnreal.div_le_iff',
  cases m,
  { cases hj,
    apply le_refl, },
  refine le_trans _ (le_max_left _ _),
  dsimp [c₀_aux],
  apply nnreal.div_le_div_left_of,
  rw lt_inf'_iff,
  intros b mem,
  exact w b,
  refine inf'_le _ _,
  exact mem_range_succ_iff.mpr hj,
  exact pos_iff_ne_zero.1 (w j),
  apply pos_iff_ne_zero.1,
  apply fact.out,
  apply pos_iff_ne_zero.1,
  rw [←add_lt_add_iff_right (1 : ℝ≥0), sub_add_cancel_of_le],
  simp only [zero_add],
  apply fact.out,
  apply le_of_lt,
  apply fact.out,
  apply pos_iff_ne_zero.1,
  apply fact.out,
end

end

end universal_constants

end thm95

end
