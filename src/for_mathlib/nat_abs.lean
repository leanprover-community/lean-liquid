
import data.real.nnreal

open_locale nnreal

-- move this
lemma cast_nat_abs {R : Type*} [linear_ordered_ring R] : ∀ (n : ℤ), (n.nat_abs : R) = abs n
| (n : ℕ) := by simp only [int.nat_abs_of_nat, int.cast_coe_nat, nat.abs_cast]
| -[1+n]  := by simp only [int.nat_abs, int.cast_neg_succ_of_nat, abs_neg,
                           ← nat.cast_succ, nat.abs_cast]

lemma cast_nat_abs_eq_nnabs_cast (n : ℤ) :
  (n.nat_abs : ℝ≥0) = real.nnabs n :=
by { ext, rw [nnreal.coe_nat_cast, cast_nat_abs, nnreal.coe_nnabs] }
