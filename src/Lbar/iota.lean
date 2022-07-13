import breen_deligne.eg
import thm95.constants
import polyhedral_lattice.int
import system_of_complexes.shift_sub_id

open breen_deligne thm95.universal_constants
open_locale nnreal

namespace Lbar

variables (r r' : ℝ≥0)
variables [fact (0 < r')] [fact (r < 1)]
variables (i : ℕ)

-- move me
lemma κ_pos : ∀ m, 0 < eg.κ r r' m
| 0 := zero_lt_one
| (m+1) := begin
  dsimp only [eg.κ, data.κ],
  refine mul_pos _ _,
  { refine nnreal.inv_pos.mpr (lt_max_of_lt_left zero_lt_one), },
  { refine mul_pos (pow_pos (fact.out _) _) (κ_pos _), }
end

variables [fact (0 < r)] [fact (r < r')] [fact (r' < 1)]

noncomputable!
def ι' : ℕ → ℝ≥0
| 0 := max
        (c₀ r r' eg (λ (n : ℕ), eg.κ r r' n) (eg.κ' r r') (i + 1) ⟨ℤ⟩)
        (c₀ r r' eg (λ (n : ℕ), eg.κ r r' n) (eg.κ' r r') (i + 1 + 1) ⟨ℤ⟩)
| (j+1) := max
        (max (j+1) (ι' j))
        (max
          (max
            (k (eg.κ' r r') i ^ 2 * ι' j)
            (k (eg.κ' r r') (i+1) ^ 2 * ι' j))
            ((k (eg.κ' r r') (i+1+1) ^ 2 * ι' j)))

lemma hι' : monotone (ι' r r' i) :=
begin
  apply monotone_nat_of_le_succ,
  rintro (_|j); refine le_trans (le_max_right _ _) (le_max_left _ _),
end

lemma Hι1 : ∀ j,
  c₀ r r' eg (λ (n : ℕ), eg.κ r r' n) (eg.κ' r r') (i + 1) ⟨ℤ⟩ ≤ ι' r r' i j
| 0 := le_max_left _ _
| (j+1) := (Hι1 j).trans $ by { apply hι', apply nat.le_succ }

lemma Hι1' : ∀ j,
  c₀ r r' eg (λ (n : ℕ), eg.κ r r' n) (eg.κ' r r') (i + 1 + 1) ⟨ℤ⟩ ≤ ι' r r' i j
| 0 := le_max_right _ _
| (j+1) := (Hι1' j).trans $ by { apply hι', apply nat.le_succ }

lemma Hι2a : ∀ j,
  k (eg.κ' r r') i ^ 2 * ι' r r' i j ≤ ι' r r' i (j + 1) :=
by rintro (_|j); simp only [ι', le_max_iff, le_rfl, true_or, or_true]

lemma Hι2b : ∀ j,
  k (eg.κ' r r') (i + 1) ^ 2 * ι' r r' i j ≤ ι' r r' i (j + 1) :=
by rintro (_|j); simp only [ι', le_max_iff, le_rfl, true_or, or_true]

lemma Hι2c : ∀ j,
  k (eg.κ' r r') (i + 1 + 1) ^ 2 * ι' r r' i j ≤ ι' r r' i (j + 1) :=
by rintro (_|j); simp only [ι', le_max_iff, le_rfl, true_or, or_true]

noncomputable
def ι : ulift.{1} ℕ → ℝ≥0 := ι' r r' i ∘ ulift.down

lemma hι : monotone (ι r r' i) :=
λ j₁ j₂ h, by { delta ι, apply hι', exact h }

lemma hι'_self_le : ∀ j:ℕ, (j:ℝ≥0) ≤ ι' r r' i j
| 0 := by { norm_cast, exact zero_le' }
| (j+1) := by { refine (le_max_left _ _).trans (le_max_left _ _) }

lemma sufficiently_increasing_eg (s : ℝ≥0) (m : ℕ) :
  ∃ n : ℕ, s ≤ ι' r r' i n * eg.κ r r' m :=
begin
  let κ := eg.κ r r' m,
  let n := ⌈s * κ⁻¹⌉₊,
  let ι := ι' r r' i n,
  refine ⟨n, _⟩,
  calc s = s * κ⁻¹ * κ : _
     ... ≤ ι * κ : mul_le_mul' _ le_rfl,
  { rw inv_mul_cancel_right₀, apply ne_of_gt, apply κ_pos, },
  { refine (nat.le_ceil _).trans (hι'_self_le _ _ _ _) }
end

lemma sufficiently_increasing_eg' (s : ℝ≥0) (m : ℕ) :
  ∃ n : ℕ, s ≤ r' * (ι' r r' i n * eg.κ r r' m) :=
begin
  obtain ⟨n,hn⟩ := sufficiently_increasing_eg r r' i (s / r') m,
  use n,
  replace hn := mul_le_mul (le_refl r') hn (zero_le (s / r')) (zero_le _),
  refine le_trans (le_of_eq _) hn,
  have : r' ≠ 0, { symmetry, exact ne_of_lt (fact.out (0 < r')) },
  rw mul_comm,
  exact (div_eq_iff this).mp rfl
end

def sufficiently_increasing
  (κ : ℝ≥0 → ℕ → ℝ≥0) (ι : ulift ℕ → ℝ≥0) : Prop :=
∀ (r : ℝ≥0) (m : ℕ), ∃ n : ℕ, r ≤ κ (ι ⟨n⟩) m

end Lbar
