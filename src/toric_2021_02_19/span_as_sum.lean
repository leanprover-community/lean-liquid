import tactic
import linear_algebra.finsupp
import algebra.ring.basic
import ring_theory.subring
import algebra.algebra.basic

open function

variables (R : Type*)

section Rnnoneg

variables [ordered_semiring R]

/--  The subtype of non-negative elements of `R`. -/
def pR : subsemiring R :=
{ carrier := {r : R | 0 ≤ r},
  one_mem' := by simp only [set.mem_set_of_eq, zero_le_one],
  mul_mem' := λ x y (x0 : 0 ≤ x) (y0 : 0 ≤ y), mul_nonneg x0 y0,
  zero_mem' := rfl.le,
  add_mem' := λ x y (x0 : 0 ≤ x) (y0 : 0 ≤ y), add_nonneg x0 y0 }

variable {R}

@[simp] lemma mem_pR_nonneg (y : (pR R)) : 0 ≤ y := y.2

namespace yes_hom

/--  The ring homomorphism `f : N → Z` is injective and its image only contains
non-negative elements. -/
structure is_inj_nonneg {N Z : Sort*} [has_zero Z] [has_le Z] (f : N → Z) : Prop :=
(inj : injective f)
(map_nonneg : ∀ n : N, 0 ≤ f n)

namespace is_inj_nonneg

open is_inj_nonneg

lemma pR_ocr (Z : Type*) [ordered_comm_semiring Z] :
  is_inj_nonneg (algebra_map (pR Z) Z) := --tidy works
⟨subtype.coe_injective, λ n, n.2⟩

lemma pR_int_int : is_inj_nonneg (algebra_map (pR ℤ) ℤ) :=
by convert pR_ocr ℤ

lemma nat (Z : Sort*) [ordered_semiring Z] [nontrivial Z] :
  is_inj_nonneg (nat.cast_ring_hom Z) :=
⟨@nat.cast_injective Z _ _ ordered_semiring.to_char_zero, λ n, nat.cast_nonneg n⟩


/--  The ring homomorphism `f : N → Z` is injective and its image only contains
non-negative elements. -/
def is_inj_nonneg {N Z : Sort*} [semiring N] [semiring Z] [has_le Z] (f : N →+* Z) : Prop :=
  injective f ∧ ∀ n : N, 0 ≤ f n

namespace is_inj_nonneg

open is_inj_nonneg

lemma pR_ocr (Z : Type*) [ordered_comm_semiring Z] :
  is_inj_nonneg (algebra_map (pR Z) Z) := --tidy works
⟨subtype.coe_injective, λ n, n.2⟩

lemma pR_int_int : is_inj_nonneg (algebra_map (pR ℤ) ℤ) :=
by convert pR_ocr ℤ

lemma nat_of_char_zero (Z : Sort*) [ordered_semiring Z] [char_zero Z] :
  is_inj_nonneg (nat.cast_ring_hom Z) :=
⟨nat.cast_injective, λ n, nat.cast_nonneg n⟩

lemma nat_of_nontrivial (Z : Sort*) [ordered_semiring Z] [nontrivial Z] :
  is_inj_nonneg (nat.cast_ring_hom Z) :=
⟨@nat.cast_injective Z _ _ ordered_semiring.to_char_zero, λ n, nat.cast_nonneg n⟩

lemma nat_int : is_inj_nonneg (nat.cast_ring_hom ℤ) :=
⟨λ a b h, by { dsimp at h, simpa using h }, λ n, by simp⟩



lemma pR_Z_eq_N : pR ℤ ≃+* ℕ := sorry

end is_inj_nonneg

end yes_hom


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
