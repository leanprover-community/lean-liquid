import tactic
import linear_algebra.finsupp
import algebra.ring.basic
import ring_theory.subring
import algebra.algebra.basic

variables (R : Type*)

section Rnnoneg

variables [ordered_semiring R]

/--  The subtype of non-negative elements of `R`. -/
def pR : subsemiring R :=
{ carrier := {r : R | 0 ≤ r},
  one_mem' := by simp only [set.mem_set_of_eq, zero_le_one],
  mul_mem' := begin
    rintros x y (x0 : 0 ≤ x) (y0 : 0 ≤ y),
    exact mul_nonneg x0 y0,
  end,
  zero_mem' := rfl.le,
  add_mem' := begin
    rintros x y (x0 : 0 ≤ x) (y0 : 0 ≤ y),
    exact add_nonneg x0 y0,
  end }

variable {R}

@[simp] lemma mem_pR_nonneg (y : (pR R)) : 0 ≤ y := y.2

/-
instance : has_coe (pR ℤ) ℕ :=
{ coe := λ ⟨h, hh⟩, int.to_nat h }

instance : has_coe ℕ (pR ℤ) :=
{ coe := λ h, h }


lemma pRZ : ℕ ≃ pR ℤ :=
{ to_fun := λ n, n,
  inv_fun := λ ⟨h, hh⟩, int.to_nat h,
  left_inv := begin
    intros x,
    dsimp at *,
    induction x with x hx,
    { refl },
    {
      rw [nat.succ_eq_add_one],
      tidy?,
      simp,
      conv_lhs {
        rw int.coe_nat_add x 1,
      },
      simp [hx],
    },
  end,
  right_inv := _ }

#exit

-/

variables {α β : Type*}

open function

end Rnnoneg

variables [ordered_comm_ring R]

instance pos_algebra : algebra (pR R) R := algebra.of_subsemiring (pR R)
