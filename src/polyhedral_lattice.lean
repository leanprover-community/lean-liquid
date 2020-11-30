import analysis.normed_space.basic
import linear_algebra.basis

universe variables u

/-!
### Definition

A *polyhedral lattice* is a finite free abelian group `Λ`
equipped with a norm `||·|| : Λ ⊗ R → R`
(so `Λ ⊗ R` is a Banach space)
that is given by the supremum of finitely many linear functions on `Λ`
with rational coefficients;
equivalently,
the “unit ball” `{λ ∈ Λ ⊗ R | ||λ|| ≤ 1}` is a rational polyhedron.

See the paragraph before Thm 9.5 of [Analytic].
-/

open finset

class polyhedral_lattice (Λ : Type u) extends normed_group Λ :=
(exists_finite_basis : ∃ {ι : Type} [fintype ι] (v : ι → Λ), is_basis ℤ v)
(is_polyhedral : ∃ {ι : Type} [nonempty ι] [fintype ι] (f : ι → Λ → ℚ),
                  ∀ x : Λ, ∥x∥ = finset.max' (finset.image (λ i : ι, f i x) univ)
                                  (nonempty.image univ_nonempty _))
