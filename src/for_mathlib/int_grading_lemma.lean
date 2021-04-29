import for_mathlib.grading
import ring_theory.noetherian -- for the lemma we need for Gordan

/-

## A technical lemma about Noetherian ℤ-graded rings

We need the following theorem for Gordan's Lemma:

If A is ℤ-graded and Noetherian then A_{≥0} is a finitely-generated A₀-algebra

-/

namespace add_monoid_grading

open direct_sum

def zero_piece_subsemiring (R : Type*) [semiring R] (A : Type*) [add_monoid A]
  [decidable_eq A] (Mᵢ : A → add_submonoid R)
  [has_add_submonoid_decomposition Mᵢ] [add_submonoid.is_gmonoid Mᵢ] : subsemiring R :=
{
  one_mem' := add_submonoid.is_gmonoid.grading_one,
  mul_mem' := λ r s, begin
    suffices : r ∈ Mᵢ 0 → s ∈ Mᵢ 0 → r * s ∈ Mᵢ (0 + 0),
      simpa,
    exact add_submonoid.is_gmonoid.grading_mul,
  end,
  ..Mᵢ 0
}

def zero_piece_subring {R : Type*} [ring R] {A : Type*} [add_monoid A]
  [decidable_eq A] (Mᵢ : A → add_submonoid R)
  [has_add_submonoid_decomposition Mᵢ] [add_submonoid.is_gmonoid Mᵢ] :
  subring R :=
{ neg_mem' := sorry,
  ..zero_piece_subsemiring R A Mᵢ,
}

def nonneg_piece_subring_of_int_grading (R : Type*) [ring R] (Mᵢ : ℤ → add_submonoid R)
  [has_add_submonoid_decomposition Mᵢ] [add_submonoid.is_gmonoid Mᵢ] : subsemiring R :=
sorry
-- { carrier := {r : R | ∀ ⦃n : ℤ⦄, n < 0 → g.decomposition a n = 0 },
--   zero_mem' := λ n _, by { rw g.decomposition.map_zero, refl },
--   add_mem' := λ a b ha hb n hn, by
--   { rw [g.decomposition.map_add, dfinsupp.add_apply, ha hn, hb hn, zero_add] },
--   one_mem' := λ n hn, (g.mem_piece_iff_single_support 1 0).1 g.one_mem (ne_of_lt hn),
--   mul_mem' := λ a b ha hb n hn, sorry }

--theorem nonnegative_subalgebra_fg_over_zero_subalgebra_of_int_grading_of_noeth
--  (A : Type*) [comm_ring A] [is_noetherian_ring A] (g : add_monoid_grading ℤ A) :

end add_monoid_grading
