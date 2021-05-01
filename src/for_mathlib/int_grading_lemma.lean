import for_mathlib.grading
import ring_theory.noetherian -- for the lemma we need for Gordan
import ring_theory.finiteness

/-

## A technical lemma about Noetherian ℤ-graded rings

We need the following theorem for Gordan's Lemma:

If A is ℤ-graded and Noetherian then A_{≥0} is a finitely-generated A₀-algebra

-/

-- move this, if it's not there already
def subring.incl (R : Type) [comm_ring R] (A B : subring R) (h : A ≤ B) : A →+* B :=
{ to_fun := λ a, ⟨a.1, h a.2⟩,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

namespace direct_sum

namespace has_add_submonoid_decomposition

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

def subsemiring_of_add_submonoid (A : Type*) [decidable_eq A] [add_monoid A] (R : Type*) [semiring R]
  (Mᵢ : A → add_submonoid R) [has_add_submonoid_decomposition Mᵢ] [add_submonoid.is_gmonoid Mᵢ]
    (S : add_submonoid A) : subsemiring R :=
 { carrier := {r : R | ∀ ⦃a : A⦄, a ∉ S → add_submonoid_decomposition Mᵢ r a = 0 },
   zero_mem' := λ n _, by { rw (add_submonoid_decomposition Mᵢ).map_zero, refl },
   add_mem' := λ a b ha hb n hn, by
   { rw [(add_submonoid_decomposition Mᵢ).map_add, dfinsupp.add_apply, ha hn, hb hn, zero_add] },
   one_mem' := λ n hn, (mem_piece_iff_single_support 1 0).1
     (add_submonoid.is_gmonoid.grading_one) (λ h, hn $ by { rw h, exact S.zero_mem }),
  -- mul_mem' := λ a b ha hb n hn, begin
  --   change ((add_submonoid_decomposition_ring_equiv Mᵢ) (a * b)) n = 0,
  --   rw ring_equiv.map_mul,
  --   -- several ways to go here, not sure which is best
  --   sorry
    mul_mem' := λ a b,
    let a' := add_submonoid_decomposition Mᵢ a in
    let b' := add_submonoid_decomposition Mᵢ b in
    λ (ha : ∀ ai ∉ S, a' ai = 0) (hb : ∀ bi ∉ S, b' bi = 0) n hn, begin
      change ((add_submonoid_decomposition_ring_equiv Mᵢ) (a * b)) n = 0,
      rw ring_equiv.map_mul,
      change (a' * b') n = 0,
      classical,
      rw direct_sum.mul_apply,
      apply dfinsupp.sum_eq_zero,
      intros ai hai,
      apply dfinsupp.sum_eq_zero,
      intros bi hbi,
      apply dif_neg,
      rintro rfl,
      obtain (hna | hnb) := S.not_mem_or_of_add_not_mem hn,
      exact hai (ha _ hna),
      exact hbi (hb _ hnb),
    end }

end has_add_submonoid_decomposition

namespace has_add_subgroup_decomposition

def zero_piece_subring {R : Type*} [ring R] {A : Type*} [add_monoid A]
  [decidable_eq A] (Gᵢ : A → add_subgroup R)
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] :
  subring R :=
{
  one_mem' := add_subgroup.is_gmonoid.grading_one,
  mul_mem' := λ r s, begin
    suffices : r ∈ Gᵢ 0 → s ∈ Gᵢ 0 → r * s ∈ Gᵢ (0 + 0),
      simpa,
    exact add_subgroup.is_gmonoid.grading_mul,
  end,
  ..Gᵢ 0
}

-- would love to deduce this from subsemiring_of_add_submonoid but it's all too much
-- for `convert` because an external direct sum of `Gᵢ i` is quite different to
-- an external direct sum of `(Gᵢ i).to_add_submonoid`
def subring_of_add_subgroup (A : Type*) [decidable_eq A] [add_monoid A] (R : Type*) [ring R]
  (Gᵢ : A → add_subgroup R) [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ]
    (S : add_submonoid A) : subring R :=
 { carrier := {r : R | ∀ ⦃a : A⦄, a ∉ S → add_subgroup_decomposition Gᵢ r a = 0 },
   zero_mem' := λ n _, by { rw (add_subgroup_decomposition Gᵢ).map_zero, refl },
   add_mem' := λ a b ha hb n hn, by
   { rw [(add_subgroup_decomposition Gᵢ).map_add, dfinsupp.add_apply, ha hn, hb hn, zero_add] },
   neg_mem' := λ a ha n hn, by
   { rw [(add_subgroup_decomposition Gᵢ).map_neg],
     convert dfinsupp.neg_apply _ n,
     rw ha hn,
     simp },
    one_mem' := λ n hn, (mem_piece_iff_single_support 1 0).1
     (add_subgroup.is_gmonoid.grading_one) (λ h, hn $ by { rw h, exact S.zero_mem }),
   mul_mem' := λ a b,
    let a' := add_subgroup_decomposition Gᵢ a in
    let b' := add_subgroup_decomposition Gᵢ b in
    λ (ha : ∀ ai ∉ S, a' ai = 0) (hb : ∀ bi ∉ S, b' bi = 0) n hn, begin
      change ((add_subgroup_decomposition_ring_equiv Gᵢ) (a * b)) n = 0,
      rw ring_equiv.map_mul,
      change (a' * b') n = 0,
      classical,
      rw has_add_submonoid_decomposition.direct_sum.mul_apply,
      apply dfinsupp.sum_eq_zero,
      intros ai hai,
      apply dfinsupp.sum_eq_zero,
      intros bi hbi,
      apply dif_neg,
      rintro rfl,
      obtain (hna | hnb) := S.not_mem_or_of_add_not_mem hn,
      exact hai (ha _ hna),
      exact hbi (hb _ hnb),
    end,
 }

def nonneg_piece_subring_of_int_grading {R : Type*} [ring R] (Gᵢ : ℤ → add_subgroup R)
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] : subring R :=
subring_of_add_subgroup ℤ R Gᵢ
{ carrier := {n : ℤ | 0 ≤ n},
  zero_mem' := le_refl (0 : ℤ),
  add_mem' := @add_nonneg ℤ _ }

-- doesn't seem to fire
instance (R : Type*) [comm_ring R] (Gᵢ : ℤ → add_subgroup R)
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] :
  algebra (zero_piece_subring Gᵢ) (nonneg_piece_subring_of_int_grading Gᵢ) :=
ring_hom.to_algebra $ subring.incl R (zero_piece_subring Gᵢ) (nonneg_piece_subring_of_int_grading Gᵢ)
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
  (A : Type*) [comm_ring A] [is_noetherian_ring A] (Gᵢ : ℤ → add_subgroup A)
  [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ] :
@algebra.finite_type (zero_piece_subring Gᵢ) (nonneg_piece_subring_of_int_grading Gᵢ) _ _
(direct_sum.has_add_subgroup_decomposition.nonneg_piece_subring_of_int_grading.algebra A Gᵢ)
:=
begin
  sorry
end

end has_add_subgroup_decomposition

end direct_sum
