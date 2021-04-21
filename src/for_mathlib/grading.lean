/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import algebra.direct_sum
import algebra.monoid_algebra -- to check we can grade a monoid algebra
import data.polynomial -- to check we can grade a polynomial ring
/-!

# Grading of a ring by a monoid

Following an idea of Eric Wieser we introduce the concept of a grading
of a ring by a module, and prove that our definition is workable
by showing that the polynomial ring `R[X]` is graded by ℕ and the
monoid algebra `R[M]` is graded by `M`.

Most of the hard work was done by Eric and Damiano.

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

end direct_sum

end Eric_PR

/-- If `M` is an additive monoid, then an `M`-grading on a ring `R` is a decomposition of `R` as
    an internal direct sum `R = ⨁Rₘ` into submonoids indexed by `m : M`, where the decomposition
    respects `1` and `*`, in the sense that `1 ∈ R₀` and `Rₘ*Rₙ ⊆ R_{m+n}` -/
structure add_monoid_grading (M : Type*) [add_monoid M] [decidable_eq M] (R : Type*) [semiring R] :=
(graded_piece : M → add_submonoid R)
(direct_sum : direct_sum.add_submonoid_is_internal graded_piece)
(grading_one : (1 : R) ∈ graded_piece 0)
(grading_mul : ∀ (m n : M) (r s : R),
  r ∈ graded_piece m → s ∈ graded_piece n → r * s ∈ graded_piece (m + n))

/-- If `M` is a monoid, then an `M`-grading on a ring `R` is a decomposition of `R` as
    an internal direct sum `R = ⨁Rₘ` into submonoids indexed by `m : M`, where the decomposition
    respects `1` and `*`, in the sense that `1 ∈ R₁` and `Rₘ*Rₙ ⊆ R_{m*n}` -/
structure monoid_grading (M : Type*) [monoid M] [decidable_eq M] (R : Type*) [semiring R] :=
(graded_piece : M → add_submonoid R)
(grading_one : (1 : R) ∈ graded_piece 1)
(grading_mul : ∀ (m n : M) (r s : R),
  r ∈ graded_piece m → s ∈ graded_piece n → r * s ∈ graded_piece (m * n))
(direct : direct_sum.add_submonoid_is_internal graded_piece)

attribute [to_additive] monoid_grading

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
