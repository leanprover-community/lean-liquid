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

variables {α β : Type*}

open function

/-- Pullback an `ordered_comm_monoid` under an injective map. -/
@[to_additive function.injective.ordered_add_comm_monoid
"Pullback an `ordered_add_comm_monoid` under an injective map."]
def function.injective.ordered_comm_monoid [ordered_comm_monoid α] {β : Type*}
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_comm_monoid β :=
{ mul_le_mul_left := λ a b ab c,
    show f (c * a) ≤ f (c * b), by simp [mul, mul_le_mul_left' ab],
  lt_of_mul_lt_mul_left :=
    λ a b c bc, @lt_of_mul_lt_mul_left' _ _ (f a) _ _ (by rwa [← mul, ← mul]),
  ..partial_order.lift f hf,
  ..hf.comm_monoid f one mul }

/-- Pullback an `ordered_cancel_comm_monoid` under an injective map. -/
@[to_additive function.injective.ordered_cancel_add_comm_monoid
"Pullback an `ordered_cancel_add_comm_monoid` under an injective map."]
def function.injective.ordered_cancel_comm_monoid [ordered_cancel_comm_monoid α] {β : Type*}
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_cancel_comm_monoid β :=
{ le_of_mul_le_mul_left := λ a b c (ab : f (a * b) ≤ f (a * c)),
    (by { rw [mul, mul] at ab, exact le_of_mul_le_mul_left' ab }),
  ..hf.left_cancel_semigroup f mul,
  ..hf.right_cancel_semigroup f mul,
  ..hf.ordered_comm_monoid f one mul }

/-- Pullback an `ordered_semiring` under an injective map. -/
def function.injective.ordered_semiring {β : Type*} [ordered_semiring α]
  [has_zero β] [has_one β] [has_add β] [has_mul β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_semiring β :=
{ zero_le_one := show f 0 ≤ f 1, by  simp only [zero, one, zero_le_one],
  mul_lt_mul_of_pos_left := λ  a b c ab c0, show f (c * a) < f (c * b),
    begin
      rw [mul, mul],
      refine mul_lt_mul_of_pos_left ab _,
      rwa ← zero,
    end,
  mul_lt_mul_of_pos_right := λ a b c ab c0, show f (a * c) < f (b * c),
    begin
      rw [mul, mul],
      refine mul_lt_mul_of_pos_right ab _,
      rwa ← zero,
    end,
  ..hf.ordered_cancel_add_comm_monoid f zero add,
  ..hf.semiring f zero one add mul }

instance : ordered_semiring (pR R) :=
subtype.coe_injective.ordered_semiring (@coe (pR R) R _)  rfl rfl (λ _ _, rfl) (λ _ _, rfl)

end Rnnoneg

variables [ordered_comm_ring R]

instance pos_algebra : algebra (pR R) R := algebra.of_subsemiring (pR R)
