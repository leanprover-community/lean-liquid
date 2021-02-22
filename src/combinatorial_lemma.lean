import algebra.group.basic
import analysis.convex.cone
import normed_group.NormedGroup
import Mbar.basic
import polyhedral_lattice.basic
import normed_group.pseudo_normed_group

/-!
In this file we state and prove lemmas 9.7 and 9.8 of [Analytic].
-/

open_locale nnreal big_operators

section lem97

variables (Λ : Type*) [add_comm_group Λ]

lemma abs_add_eq_add_abs_iff (a b : ℤ) :
  abs (a + b) = abs a + abs b ↔ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) :=
begin
  sorry
end

/-- Lemma 9.7 of [Analytic]. -/
lemma lem97 (hΛ_tf : torsion_free Λ) [hΛ_fg : module.finite ℤ Λ]
  (N : ℕ) (s : finset Λ) :
  ∃ F : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ F) (y : Λ →+ ℤ),
    x - x' = N • y ∧
    ∀ a ∈ s, (0 ≤ x' a ∧ 0 ≤ (x - x') a) ∨ (x' a ≤ 0 ∧ (x - x') a ≤ 0) :=
begin
  sorry
end

end lem97

open pseudo_normed_group


variables (Λ : Type*) (r' : ℝ≥0) (S : Type*)
variables [fintype S] [normed_group Λ] [polyhedral_lattice Λ]

lemma lem98 (N : ℕ) (hn : 0 < N) :
  ∃ d, ∀ c (x : Λ →+ Mbar r' S) (hx : x ∈ filtration (Λ →+ Mbar r' S) c),
    ∃ y : fin N → (Λ →+ Mbar r' S),
      (x = ∑ i, y i) ∧
      (∀ i, y i ∈ filtration (Λ →+ Mbar r' S) (c/N + d)) :=
begin
  sorry
end
