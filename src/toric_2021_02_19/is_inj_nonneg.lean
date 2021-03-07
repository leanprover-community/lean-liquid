import algebra.algebra.basic

open function

variables (R : Type*)

section nnR

variables [ordered_semiring R]

/--  The subtype of non-negative elements of `R`. -/
def nnR : subsemiring R :=
{ carrier := {r : R | 0 ≤ r},
  one_mem' := by simp only [set.mem_set_of_eq, zero_le_one],
  mul_mem' := λ x y (x0 : 0 ≤ x) (y0 : 0 ≤ y), mul_nonneg x0 y0,
  zero_mem' := rfl.le,
  add_mem' := λ x y (x0 : 0 ≤ x) (y0 : 0 ≤ y), add_nonneg x0 y0 }

variable {R}

variables {N Z : Type*}

@[simp] lemma mem_nnR_nonneg (y : (nnR R)) : 0 ≤ y := y.2

/--  The function `f : N → Z` is injective and its image only contains non-negative elements.
These properties are useful for `pointed_of_is_basis_is_inj`, in order to avoid having getting
entangled into statements such as "the subtype of the non-negative terms in ℤ is the type of ℕ". -/
structure is_inj_nonneg [has_zero Z] [has_le Z] (f : N → Z) : Prop :=
(inj : injective f)
(map_nonneg : ∀ n : N, 0 ≤ f n)

namespace is_inj_nonneg

variable (Z)

/--  The inclusion of the natural numbers into a non-trivial `ordered_semiring` is injective and
consists of non-negative elements. -/
lemma nat [ordered_semiring Z] [nontrivial Z] :
  is_inj_nonneg (nat.cast_ring_hom Z) :=
⟨@nat.cast_injective Z _ _ ordered_semiring.to_char_zero, λ n, nat.cast_nonneg n⟩

/--  The inclusion of the non-negative elements of an `ordered_comm_semiring` is injective and
consists of non-negative elements. -/
lemma nnR_ocr [ordered_comm_semiring Z] :
  is_inj_nonneg (algebra_map (nnR Z) Z) := --tidy works
⟨subtype.coe_injective, λ n, n.2⟩

/--  The inclusion of the non-negative integers into the integers is injective and
consists of non-negative elements. -/
lemma nnR_int_int : is_inj_nonneg (algebra_map (nnR ℤ) ℤ) :=
by convert nnR_ocr ℤ

end is_inj_nonneg

end nnR

instance nnR_algebra [ordered_comm_ring R] : algebra (nnR R) R := algebra.of_subsemiring (nnR R)
