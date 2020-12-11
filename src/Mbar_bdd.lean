import data.fintype.intervals
import data.real.basic
import algebra.big_operators.basic
import category_theory.Fintype

noncomputable theory
open_locale big_operators classical

-- Thanks to Ruben Van de Velde and Yury G. Kudryashov for help with
-- the Ico_finite and Icc_finite lemmas.
-- TODO: Move these somewhere...
open set
lemma Ico_finite (a b : ℤ) : set.finite (Ico a b) := ⟨set.Ico_ℤ_fintype a b⟩
lemma Icc_finite (a b : ℤ) : set.finite (Icc a b) :=
begin
  convert Ico_finite a (b+1),
  ext,
  simp [int.lt_add_one_iff],
end

instance (a b : ℤ) : fintype (Icc a b) := nonempty.some (Icc_finite a b)

def Mbar_bdd (r : ℝ) (hr : 0 < r) (S : Fintype) (c : ℝ) (M : ℕ) :=
{F : S → fin (M + 1) → ℤ |
  (∀ s, F s 0 = 0) ∧
  (∑ s i, abs (F s i : ℝ) * r^i.1 ≤ c) }

-- for mathlib?
namespace finset

/-- A variant of single_le_sum with a explicit -/
def single_le_sum' {α : Type*} {β : Type*} {s : finset α} {f : α → β} [ordered_add_comm_monoid β] :
    (∀ (x : α), x ∈ s → 0 ≤ f x) → ∀ (a : α), a ∈ s → f a ≤ ∑ (x : α) in s, f x :=
single_le_sum

end finset

open finset

lemma Mbar_bdd_coeff_bound {r : ℝ} (hr : 0 < r) {S : Fintype} {c : ℝ} {M : ℕ}
  (F : S → fin (M + 1) → ℤ) (hF : ∑ s i, abs (F s i : ℝ) * r^i.1 ≤ c) (n : fin (M + 1)) (s : S) :
  abs (F s n : ℝ) ≤ c / min (r ^ M) 1 :=
begin
  rw le_div_iff (lt_min (pow_pos hr _) zero_lt_one),
  calc abs ↑(F s n) * min (r ^ M) 1 ≤ abs ↑(F s n) * r ^ n.1 : begin
    refine mul_le_mul_of_nonneg_left _ (abs_nonneg _),
    cases le_or_lt r 1 with hr1 hr1,
    { refine le_trans (min_le_left _ _) _,
      exact pow_le_pow_of_le_one (le_of_lt hr) hr1 (nat.lt_add_one_iff.1 n.2) },
    { exact le_trans (min_le_right _ _) (one_le_pow_of_one_le (le_of_lt hr1) _) },
  end
  ... ≤ ∑ i, abs (F s i : ℝ) * r^i.1 : begin
    refine single_le_sum' (λ _ _, _) n (mem_univ _),
    exact mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt hr) _),
  end
  ... ≤ ∑ s i, abs (F s i : ℝ) * r^i.1 : begin
    refine single_le_sum' (λ _ _, _) s (mem_univ _),
    exact sum_nonneg (λ _ _, mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt hr) _)),
  end
  ... ≤ c : hF
end

private def temp_map {r : ℝ} (hr : 0 < r) {S : Fintype} {c : ℝ} {M : ℕ} (F : Mbar_bdd r hr S c M)
  (n : fin (M + 1)) (s : S) : Icc (ceil (-(c / min (r ^ M) 1))) (floor (c / min (r ^ M) 1)) :=
let h := abs_le.1 $ Mbar_bdd_coeff_bound hr F.1 F.2.2 n s in
⟨F.1 s n, ceil_le.2 $ h.1, le_floor.2 h.2⟩

lemma Mbar_bdd_finset {r : ℝ} (hr : 0 < r) {S : Fintype} {c : ℝ} {M : ℕ} :
  fintype (Mbar_bdd r hr S c M) :=
fintype.of_injective (temp_map hr) begin
  rintros ⟨f1, hf1⟩ ⟨f2, hf2⟩ h,
  ext s n,
  change (temp_map hr ⟨f1, hf1⟩ n s).1 = (temp_map hr ⟨f2, hf2⟩ n s).1,
  rw h,
end
