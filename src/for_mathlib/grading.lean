/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import algebra.direct_sum
import algebra.monoid_algebra -- to check we can grade a monoid algebra
import data.polynomial -- to check we can grade a polynomial ring
import ring_theory.noetherian -- for the lemma we need for Gordan
--import for_mathlib.dfinsupp -- finsupp <-> dfinsupp
/-!

# Grading of a ring by a monoid

A grading of a ring `R` by a monoid `M` is a decomposition R ≃ ⨁ Rₘ as an internal
direct sum of subgroups indexed by `m`, satisfying 1 ∈ R₀ and RₘRₙ⊆R_{m+n}

-/

/-

The below is in PR #7190 by Eric to algebra.direct_sum

-/

section Eric_PR

namespace direct_sum

variables {ι : Type*}

open_locale direct_sum

/-- The `direct_sum` formed by a collection of `add_submonoid`s of `M` is said to be internal if the
canonical map `(⨁ i, A i) →+ M` is bijective.
See `direct_sum.add_subgroup_is_internal` for the same statement about `add_subgroup`s. -/
def add_submonoid_is_internal {M : Type*} [decidable_eq ι] [add_comm_monoid M]
  (A : ι → add_submonoid M) : Prop :=
function.bijective (direct_sum.to_add_monoid (λ i, (A i).subtype) : (⨁ i, A i) →+ M)

/-- The `direct_sum` formed by a collection of `add_subgroup`s of `M` is said to be internal if the
canonical map `(⨁ i, A i) →+ M` is bijective.
See `direct_sum.submodule_is_internal` for the same statement about `submodules`s. -/
def add_subgroup_is_internal {M : Type*} [decidable_eq ι] [add_comm_group M]
  (A : ι → add_subgroup M) : Prop :=
function.bijective (direct_sum.to_add_monoid (λ i, (A i).subtype) : (⨁ i, A i) →+ M)

lemma add_subgroup_is_internal.to_add_submonoid
  {M : Type*} [decidable_eq ι] [add_comm_group M] (A : ι → add_subgroup M) :
  add_subgroup_is_internal A ↔
    add_submonoid_is_internal (λ i, (A i).to_add_submonoid) :=
iff.rfl

-- that's the end of Eric's PR but we seem to need more: we don't have the projections!

variables {M : Type*} [decidable_eq ι] [add_comm_monoid M] (A : ι → Type*) [∀ i, add_comm_monoid (A i)]

def projection (j : ι) : (⨁ i, A i) →+ A j :=
{ to_fun := λ f, f j,
  map_zero' := rfl,
  map_add' := λ x y, x.add_apply y j }

lemma projection_of_same (j : ι) (aj : A j) : projection A j (of (λ i, A i) j aj) = aj :=
@dfinsupp.single_eq_same _ _ _ _ j _

lemma projection_of_ne {i j : ι} (h : i ≠ j) (ai : A i) :
  projection A j (of (λ i, A i) i ai) = 0 :=
dfinsupp.single_eq_of_ne h

end direct_sum

end Eric_PR

/-- If `M` is an additive monoid, then an `M`-grading on a ring `R` is a decomposition of `R` as
    an internal direct sum `R = ⨁Rₘ` into submonoids indexed by `m : M`, where the decomposition
    respects `1` and `*`, in the sense that `1 ∈ R₀` and `Rₘ*Rₙ ⊆ R_{m+n}` -/
structure add_monoid_grading (M : Type*) [add_monoid M] [decidable_eq M] (R : Type*) [semiring R] :=
(pieces : M → add_submonoid R)
(direct_sum : direct_sum.add_submonoid_is_internal pieces)
(grading_one : (1 : R) ∈ pieces 0)
(grading_mul : ∀ (m n : M) (r s : R),
  r ∈ pieces m → s ∈ pieces n → r * s ∈ pieces (m + n))

/-- If `M` is a monoid, then an `M`-grading on a ring `R` is a decomposition of `R` as
    an internal direct sum `R = ⨁Rₘ` into submonoids indexed by `m : M`, where the decomposition
    respects `1` and `*`, in the sense that `1 ∈ R₁` and `Rₘ*Rₙ ⊆ R_{m*n}` -/
structure monoid_grading (M : Type*) [monoid M] [decidable_eq M] (R : Type*) [semiring R] :=
(pieces : M → add_submonoid R)
(is_direct_sum : direct_sum.add_submonoid_is_internal pieces)
(grading_one : (1 : R) ∈ pieces 1)
(grading_mul : ∀ (m n : M) (r s : R),
  r ∈ pieces m → s ∈ pieces n → r * s ∈ pieces (m * n))

attribute [to_additive] monoid_grading

namespace monoid_grading

/-! ## graded pieces -/

section graded_pieces

variables {M : Type*} [monoid M] [decidable_eq M] {R : Type*} [semiring R]

open_locale direct_sum

/-- The equivalence between R and ⨁ m, Rₘ if R is a graded (semi)ring. -/
@[to_additive "The equivalence between R and ⨁ m, Rₘ if R is a graded (semi)ring."]
noncomputable def decomposition (g : monoid_grading M R) :
  R ≃+ ⨁ m, g.pieces m :=
(add_equiv.of_bijective _ g.is_direct_sum).symm

/-- If r : R and R is graded by M then `piece r m` is the element rₘ of Rₘ such that ∑ₘ rₘ = r.  -/
@[to_additive "If r : R and R is graded by M then `piece r m` is the element rₘ of Rₘ such that ∑ₘ rₘ = r."]
noncomputable def piece (g : monoid_grading M R) (r : R) (m : M) : R :=
direct_sum.projection (λ m, g.pieces m) m (decomposition g r)

/-- If `r ∈ Rₘ` then the element of `R` which is `r` at `m` and zero elsewhere, is `r`. -/
@[to_additive]
lemma eq_decomposition_of_mem_piece''' {g : monoid_grading M R} {r : R} {m : M}
  (hr : r ∈ g.pieces m) :
  (g.decomposition).symm (direct_sum.of (λ m, g.pieces m) m ⟨r, hr⟩) = r :=
begin
  change (direct_sum.to_add_monoid (λ m, (g.pieces m).subtype) : (⨁ m, (g.pieces m)) →+ R)
    (direct_sum.of (λ m, g.pieces m) m ⟨r, hr⟩) = r,
  rw direct_sum.to_add_monoid_of,
  refl,
end

/-- If `r ∈ Rₘ` then `r` is the element of `⨁Rₘ` which is `r` at `m` and 0 elsewhere. -/
@[to_additive]
lemma eq_decomposition_of_mem_piece'' {g : monoid_grading M R} {r : R} {m : M}
  (hr : r ∈ g.pieces m) :
  (g.decomposition) r = (direct_sum.of (λ m, g.pieces m) m ⟨r, hr⟩) :=
g.decomposition.eq_symm_apply.mp (eq_decomposition_of_mem_piece''' hr).symm

/-- If `r ∈ Rₘ` then `rₘ`, the `m`'th component of `r`, considered as an element of `Rₘ`, is `r`. -/
@[to_additive]
lemma eq_decomposition_of_mem_piece' {g : monoid_grading M R} {r : R} {m : M}
  (hr : r ∈ g.pieces m) :
  (g.decomposition) r m = ⟨r, hr⟩ :=
begin
  rw eq_decomposition_of_mem_piece'' hr,
  apply dfinsupp.single_eq_same,
end

/-- If `r ∈ Rₘ` then `rₘ`, the `m`'th component of `r`, considered as an element of `R`, is `r`. -/
@[to_additive]
lemma eq_decomposition_of_mem_piece {g : monoid_grading M R} {r : R} {m : M} (hr : r ∈ g.pieces m) :
  ((g.decomposition) r m : R) = r :=
begin
  rw eq_decomposition_of_mem_piece' hr,
  refl,
end

end graded_pieces

/-! ## rings are graded by subgroups -/

variables {M : Type*} [monoid M] [decidable_eq M] {R : Type*} [ring R]

example (A : Type) [add_comm_group A] (x y : A) : x + y = 0 → -x = y := neg_eq_of_add_eq_zero

-- to_additive can't handle the add_subgroup :-(
/-- A monoid_grading on a ring be add_submonoids is in fact by add_subgroups -/
def add_subgroup_pieces (g : monoid_grading M R) (m : M) : add_subgroup R :=
{ neg_mem' := λ x hx, begin
    change -x ∈ g.pieces m,
    convert (g.decomposition (-x) m).2,
    apply neg_eq_of_add_eq_zero,
    --  x ∈ Rₘ so (g.decomposition x).to_finsupp m = x.
    nth_rewrite 0 ← eq_decomposition_of_mem_piece hx,
    rw subtype.val_eq_coe,
    norm_cast,
    suffices : (g.decomposition x + g.decomposition (-x)) m  = 0,
      simp only [*, add_submonoid.coe_zero, direct_sum.add_apply] at *,
    simp [← (g.decomposition).map_add],
  end,
  ..g.pieces m}

end monoid_grading

namespace add_monoid_grading

def add_subgroup_pieces {M : Type*} [add_monoid M] [decidable_eq M]
  {R : Type*} [ring R]  (g : add_monoid_grading M R) (m : M) : add_subgroup R :=
{ neg_mem' := λ x hx, begin
-- same proof as above :-(
    change -x ∈ g.pieces m,
    convert (g.decomposition (-x) m).2,
    apply neg_eq_of_add_eq_zero,
    --  x ∈ Rₘ so (g.decomposition x).to_finsupp m = x.
    nth_rewrite 0 ← eq_decomposition_of_mem_piece hx,
    rw subtype.val_eq_coe,
    norm_cast,
    suffices : (g.decomposition x + g.decomposition (-x)) m  = 0,
      simp only [*, add_submonoid.coe_zero, direct_sum.add_apply] at *,
    simp [← (g.decomposition).map_add],
  end,
  ..g.pieces m}

attribute [to_additive monoid_grading.add_subgroup_pieces] add_subgroup_pieces

end add_monoid_grading


open_locale direct_sum
-- should be in algebra.direct_sum
lemma direct_sum.to_add_monoid_apply {ι : Type*} [decidable_eq ι]
  {β : ι → Type*} [Π (i : ι), add_comm_monoid (β i)]
  [ Π (i : ι) (x : β i), decidable (x ≠ 0)]
  {γ : Type*} [add_comm_monoid γ]
  (f : Π (i : ι), β i →+ γ) (b : ⨁ i, β i):
  direct_sum.to_add_monoid f b = dfinsupp.sum b (λ i, f i) :=
dfinsupp.sum_add_hom_apply _ _

/-!

## test : grading a polynomial ring

-/


section polynomials

open polynomial

open_locale direct_sum

noncomputable theory

abbreviation monomial.submonoid (R : Type) [semiring R] (i : ℕ) : add_submonoid (polynomial R) :=
(monomial i : R →ₗ polynomial R).to_add_monoid_hom.mrange

abbreviation monomial.to_submonoid (R : Type) [semiring R] (i : ℕ) : R →+ monomial.submonoid R i :=
(monomial i : R →ₗ polynomial R).to_add_monoid_hom.mrange_restrict

def polynomial_equiv (R : Type) [semiring R] :
  (⨁ i, monomial.submonoid R i) ≃+ polynomial R :=
add_monoid_hom.to_add_equiv
  (direct_sum.to_add_monoid $ λ i,
    (monomial.submonoid R i).subtype)
  (finsupp.lift_add_hom $ λ n,
    (direct_sum.of (λ i, monomial.submonoid R i) n).comp (monomial.to_submonoid R n))
  (begin
    apply direct_sum.add_hom_ext',
    rintro i,
    apply add_monoid_hom.ext,
    rintro ⟨x, r, rfl⟩,
    dsimp,
    simp [monomial],
    refl,
  end)
  (begin
    ext i r : 2,
    dsimp,
    simp [monomial],
  end).

end polynomials

/-!

## test : grading a monoid algebra

-/

namespace add_monoid_algebra

-- second test case: grading add_monoid_algebras.

variables (R ι : Type) [semiring R] (M : Type) [add_monoid M] [decidable_eq M] [decidable_eq ι]

open polynomial

open_locale direct_sum

noncomputable theory


/-- `monomial s a` is the monomial `a * X^s` -/
noncomputable def Mm (i : M) : R →ₗ[R] add_monoid_algebra R M :=
finsupp.lsingle i

abbreviation monomial.submonoid (i : M) : add_submonoid (add_monoid_algebra R M) :=
(Mm R M i : R →ₗ add_monoid_algebra R M).to_add_monoid_hom.mrange

abbreviation monomial.to_submonoid (i : M) : R →+ monomial.submonoid R M i :=
(Mm R M i : R →ₗ add_monoid_algebra R M).to_add_monoid_hom.mrange_restrict

def polynomial_equiv :
  (⨁ i, monomial.submonoid R M i) ≃+ add_monoid_algebra R M :=
add_monoid_hom.to_add_equiv
  (direct_sum.to_add_monoid $ λ i,
    (monomial.submonoid R M i).subtype)
  (finsupp.lift_add_hom $ λ n,
    (direct_sum.of (λ i, monomial.submonoid R M i) n).comp (monomial.to_submonoid R M n))
  (begin
    ext i ⟨x, r, rfl⟩ : 2,
    simpa [Mm],
  end)
  (begin
    ext i r : 2,
    simp [Mm],
  end).

end add_monoid_algebra

/-

## The theorem we need for Gordan and hence LTE

If A is ℤ-graded and Noetherian then A_{≥0} is a finitely-generated A₀-algebra

-/

namespace add_monoid_grading

def zero_piece_subsemiring (A : Type*) [semiring A] (M : Type*) [add_monoid M]
  [decidable_eq M] (g : add_monoid_grading M A) : subsemiring A :=
{
  one_mem' := g.grading_one,
  mul_mem' := λ r s, begin
    convert g.grading_mul 0 0 r s,
    rw add_zero,
    refl,
  end,
  ..g.pieces 0
}

def zero_piece_subring (A : Type*) [ring A] (M : Type*) [add_monoid M]
  [decidable_eq M] (g : add_monoid_grading M A) : subring A :=
{
  one_mem' := g.grading_one,
  mul_mem' := λ r s, begin
    convert g.grading_mul 0 0 r s,
    rw add_zero,
    refl,
  end,
  ..g.add_subgroup_pieces 0
}

--theorem zero_piece_subring_eq_decomposition_support_zero :


def nonneg_piece_subring_of_int_grading (A : Type*) [ring A]
  (g : add_monoid_grading ℤ A) : subring A :=
{ carrier := {a : A | ∀ n : ℤ, n < 0 → g.decomposition a n = 0 },
  zero_mem' := sorry,
  add_mem' := sorry,
  neg_mem' := sorry,
  one_mem' := sorry,
  mul_mem' := sorry, }

--theorem nonnegative_subalgebra_fg_over_zero_subalgebra_of_int_grading_of_noeth
--  (A : Type*) [comm_ring A] [is_noetherian_ring A] (g : add_monoid_grading ℤ A) :

end add_monoid_grading
