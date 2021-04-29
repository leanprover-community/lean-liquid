#exit
import for_mathlib.grading
import ring_theory.noetherian -- for the lemma we need for Gordan

/-

## A technical lemma about Noetherian ℤ-graded rings

The theorem we need for Gordan and hence LTE

If A is ℤ-graded and Noetherian then A_{≥0} is a finitely-generated A₀-algebra

-/

namespace add_monoid_grading

def zero_piece_subsemiring (A : Type*) [semiring A] (M : Type*) [add_monoid M]
  [decidable_eq M] (g : add_monoid_grading M A) : subsemiring A :=
{
  one_mem' := g.one_mem,
  mul_mem' := λ r s, begin
    convert g.mul_mem 0 0 r s,
    rw add_zero,
    refl,
  end,
  ..g.pieces 0
}

def zero_piece_subring {A : Type*} [ring A] {M : Type*} [add_monoid M]
  [decidable_eq M] (g : add_monoid_grading M A) : subring A :=
{
  one_mem' := g.one_mem,
  mul_mem' := λ r s, begin
    convert g.mul_mem 0 0 r s,
    rw add_zero,
    refl,
  end,
  ..g.add_subgroup_pieces 0
}

def nonneg_piece_subring_of_int_grading (A : Type*) [semiring A]
  (g : add_monoid_grading ℤ A) : subsemiring A :=
{ carrier := {a : A | ∀ ⦃n : ℤ⦄, n < 0 → g.decomposition a n = 0 },
  zero_mem' := λ n _, by { rw g.decomposition.map_zero, refl },
  add_mem' := λ a b ha hb n hn, by
  { rw [g.decomposition.map_add, dfinsupp.add_apply, ha hn, hb hn, zero_add] },
  one_mem' := λ n hn, (g.mem_piece_iff_single_support 1 0).1 g.one_mem (ne_of_lt hn),
  mul_mem' := λ a b ha hb n hn, sorry }

--theorem nonnegative_subalgebra_fg_over_zero_subalgebra_of_int_grading_of_noeth
--  (A : Type*) [comm_ring A] [is_noetherian_ring A] (g : add_monoid_grading ℤ A) :

end add_monoid_grading
