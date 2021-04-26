import algebra.monoid_algebra -- to check we can grade a monoid algebra
import data.polynomial -- to check we can grade a polynomial ring/-
import for_mathlib.grading
/-

# Examples to show how to use `grading`

-/

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
