import algebra.group.basic
import normed_group.NormedGroup

import polyhedral_lattice

/-!
In this file we state and prove lemmas 9.7 and 9.8 of [Analytic].
-/

variables (Λ : Type*) [add_comm_group Λ]

/-- Lemma 9.7 of [Analytic]. -/
lemma lem97 (hΛ_tf : torsion_free Λ) (hΛ_fg : module.finite ℤ Λ)
  (N : ℕ) (s : finset Λ) :
  ∃ F : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ F) (y : Λ →+ ℤ),
    x - x' = N • y ∧
    ∀ a ∈ s, 0 ≤ x a ↔ 0 ≤ (x - x') a :=
begin
  sorry
end
