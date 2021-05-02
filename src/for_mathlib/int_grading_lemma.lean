import for_mathlib.grading_zero_subring

/-

## A technical lemma about Noetherian ℤ-graded rings

We need the following theorem for Gordan's Lemma:

If A is ℤ-graded and Noetherian then A_{≥0} is a finitely-generated A₀-algebra

-/

namespace direct_sum

namespace has_add_subgroup_decomposition

def nonneg_piece_subring_of_int_grading {R : Type*} [ring R] (Gᵢ : ℤ → add_subgroup R)
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] : subring R :=
subring_of_add_subgroup R Gᵢ
{ carrier := {n : ℤ | 0 ≤ n},
  zero_mem' := le_refl (0 : ℤ),
  add_mem' := @add_nonneg ℤ _ }

-- doesn't seem to fire
instance (R : Type*) [comm_ring R] (Gᵢ : ℤ → add_subgroup R)
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] :
  algebra (zero_component_subring R Gᵢ) (nonneg_piece_subring_of_int_grading Gᵢ) :=
ring_hom.to_algebra $ subring.incl R
  (zero_component_subring R Gᵢ) (nonneg_piece_subring_of_int_grading Gᵢ)
begin
  intros r hr n hn,
  change r ∈ Gᵢ 0 at hr,
  change ¬0 ≤ n at hn,
  rw mem_piece_iff_single_support at hr,
  apply hr,
  apply ne_of_lt,
  exact not_le.mp hn,
end

-- Brasca lemma
lemma ft_iff_fg {R : Type*} {M : Type*} [comm_ring R] [add_comm_monoid M] [nontrivial R] :
  add_monoid.fg M ↔ algebra.finite_type R (add_monoid_algebra R M) := sorry

theorem nonnegative_subalgebra_fg_over_zero_subalgebra_of_int_grading_of_noeth
  (R : Type*) [comm_ring R] [is_noetherian_ring R] (Gᵢ : ℤ → add_subgroup R)
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] :
@algebra.finite_type (zero_component_subring R Gᵢ) (nonneg_piece_subring_of_int_grading Gᵢ) _ _
(direct_sum.has_add_subgroup_decomposition.nonneg_piece_subring_of_int_grading.algebra R Gᵢ)
:=
begin
  -- First prove Rₐ is a Noetherian R₀-module (see grading_zero_subring file)
  -- then run through proof in pdf
  sorry
end

end has_add_subgroup_decomposition

end direct_sum
