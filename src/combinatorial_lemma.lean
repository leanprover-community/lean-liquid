import algebra.group.basic
import normed_group.NormedGroup

/-!
In this file we state and prove lemmas 9.7 and 9.8 of [Analytic].
-/

section move_this

-- rewrite to include multiplicative version
def torsion_free (A : Type*) [add_comm_group A] : Prop :=
∀ (a : A) (n : ℕ), n • a = 0 → n = 0

-- do we have this in mathlib for mere groups (not modules)??
def finitely_generated (A : Type*) [add_comm_group A] : Prop :=
∃ s : finset A, ∀ a : A, a ∈ add_subgroup.closure (s : set A)

variables (Λ : Type*) [add_comm_group Λ]

/-- Lemma 9.7 of [Analytic]. -/
lemma lem97 (hΛ_tf : torsion_free Λ) (hΛ_fg : finitely_generated Λ)
  (N : ℕ) (s : finset Λ) :
  ∃ F : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ F) (y : Λ →+ ℤ),
    x - x' = N • y ∧
    ∀ a ∈ s, 0 ≤ x a ↔ 0 ≤ (x - x') a :=
begin
  sorry
end

end move_this
