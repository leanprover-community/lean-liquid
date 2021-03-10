import algebra.group.basic
import analysis.convex.cone

import polyhedral_lattice.basic

/-!
In this file we state and prove 9.7 of [Analytic].
-/

open_locale nnreal big_operators

variables (Λ : Type*) [add_comm_group Λ]

/-
### These are now all in mathlib, I think

lemma abs_smul {α : Type*} [linear_ordered_add_comm_group α] (n : ℕ) (a : α) :
  abs (n • a) = n • abs a := by admit

lemma abs_add_eq_add_abs {α : Type*} [linear_ordered_add_comm_group α]  {a b : α} (hle : a ≤ b) :
  abs (a + b) = abs a + abs b ↔ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) := by admit

lemma abs_add_eq_add_abs_iff {α : Type*} [linear_ordered_add_comm_group α]  (a b : α) :
  abs (a + b) = abs a + abs b ↔ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) := by admit

-/

/-
jmc: I don't know exactly which version of the two lemmas below
will be easier to prove, `lem97` or `lem97'`.
The first one is closer to [Analytic], but the second one is easier to use.
Mathematically they are indistinguishable.
-/

/-- Lemma 9.7 of [Analytic]. -/
lemma lem97 (hΛ_tf : torsion_free Λ) [hΛ_fg : module.finite ℤ Λ]
  {ι : Type*} [fintype ι]
  (N : ℕ) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (0 ≤ x' (l i) ∧ 0 ≤ (x - x') (l i)) ∨ (x' (l i) ≤ 0 ∧ (x - x') (l i) ≤ 0) :=
begin
  sorry
end

/-- Lemma 9.7 of [Analytic]. -/
lemma lem97' (hΛ_tf : torsion_free Λ) [hΛ_fg : module.finite ℤ Λ]
  {ι : Type*} [fintype ι]
  (N : ℕ) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (x (l i)).nat_abs = N * (y (l i)).nat_abs + (x' (l i)).nat_abs :=
begin
  sorry
end
