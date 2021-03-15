import algebra.group.basic
import analysis.convex.cone
import linear_algebra.dual

import polyhedral_lattice.basic
import toric.is_inj_nonneg
-- import toric.pairing_dual_saturated -- fae: I have commented this `import`, it gives an error


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

noncomputable theory

variables {Λ}

def explicit_dual_set {ι : Type*} (l : ι → Λ) : submodule ℕ (Λ →+ ℤ) :=
{ carrier := {x | ∀ i, 0 ≤ x (l i)},
  zero_mem' := λ i, le_rfl,
  add_mem' := λ x y hx hy i, add_nonneg (hx i) (hy i),
  smul_mem' := λ n x hx i, by { rw [add_monoid_hom.nat_smul_apply], exact nsmul_nonneg (hx i) n } }

lemma explicit_gordan (hΛ_tf : torsion_free Λ) [hΛ_fg : module.finite ℤ Λ]
  {ι : Type*} [fintype ι] (l : ι → Λ) : (explicit_dual_set l).fg :=
sorry

lemma lem97_pos {hΛ_tf : torsion_free Λ} {hΛ_fg : module.finite ℤ Λ}
  {ι : Type*} [fintype ι] {N : ℕ} (l : ι → Λ) : ∃ B : finset (explicit_dual_set l), ∀ x : Λ →+ ℤ,
  x ∈ (explicit_dual_set l) → ∃ (x' ∈ B) (y : explicit_dual_set l),
  x = N • y + x' ∧ ∀ i, x' (l i) ≤ x (l i) :=
begin
  sorry
end

section sign_vectors

variables {Λ} [add_comm_group Λ]

def nonzero_sign : ℤ → ℤ := λ n, if n ≥ 0 then 1 else -1

@[simp] def is_sign : ℤ → Prop
| (1 : ℤ) := true
| (-1 : ℤ) := true
| (n : ℤ) := false

lemma is_sign_sign : ∀ (i : ℤ), is_sign (nonzero_sign i) :=
begin
  intro i,
  by_cases hi : i ≥ 0,
  simp [nonzero_sign, if_pos hi],
  simp [nonzero_sign, if_neg hi],
end

def sign_vectors (ι : Type*) := { ε : ι → ℤ // ∀ i : ι, is_sign (ε i) }

lemma fintype_sign_vectors {ι : Type*} : fintype ι → fintype (sign_vectors ι) := sorry

--instance fintype.sign_vectors [ι : Type] [fintype ι] : fintype (sign_vectors ι) := by { apply_rules fintype_sign_vectors }
--fae: useless?

end sign_vectors

/--Given a list l of elements of Λ and a functional x, (pos_vector l x) is the sign-vector of
the values of x (l i).
-/
def pos_vector {ι : Type*} [fintype ι] (l : ι → Λ) (x : Λ →+ ℤ) : sign_vectors ι :=
begin
  let ε_0 := λ i : ι, nonzero_sign (x (l i)),
  have hε : ∀ i, is_sign (ε_0 i),
  { intro i,
    dsimp [ε_0],
    apply is_sign_sign },
  use ⟨ε_0, hε⟩,
end

lemma smul_to_explicit_dual_set {ι : Type*} [fintype ι] (l : ι → Λ) (x : Λ →+ ℤ) :
  x ∈ (explicit_dual_set ((pos_vector l x).1 • l)) := sorry

open classical

local attribute [instance] prop_decidable

variables (Λ)

/-- Given a list l, a vector of signs ε (and an integer N), (pos_A l ε) is a finite set of functionals satisfying the
requirements of Lemma 9.7 of [Analytic] with respect to all functionals which are positive on all ((ε • l) i)'s.
Its existence is established in lem97_pos.
-/
def pos_A (ι : Type*) [fintype ι] (hΛ_tf : torsion_free Λ) (hΛ_fg : module.finite ℤ Λ) (N : ℕ)
  (l : ι → Λ) (ε : sign_vectors ι) : finset (Λ →+ ℤ) := by { apply choice, apply_instance}

/-
jmc: I don't know exactly which version of the two lemmas below
will be easier to prove, `lem97` or `lem97'`.
The first one is closer to [Analytic], but the second one is easier to use.
Mathematically they are indistinguishable.
fae: I am going for the first, `lem97`. I left `lem97'` there, at any rate.
-/


/-- Lemma 9.7 of [Analytic]. -/
lemma lem97 (hΛ_tf : torsion_free Λ) [hΛ_fg : module.finite ℤ Λ]
  {ι : Type*} [fintype ι] (N : ℕ) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (0 ≤ x' (l i) ∧ 0 ≤ (x - x') (l i)) ∨ (x' (l i) ≤ 0 ∧ (x - x') (l i) ≤ 0) :=
begin
  let A := finset.bUnion (@finset.univ (sign_vectors ι) (fintype_sign_vectors _)) (pos_A Λ ι hΛ_tf hΛ_fg N l),
  use A,
  intro x,
  have : x ∈ (explicit_dual_set ((pos_vector l x).1 • l)) := smul_to_explicit_dual_set l x,
  obtain ⟨B, hB⟩ := lem97_pos ((pos_vector l x).1 • l),
  specialize hB x this,
  sorry,

  all_goals {assumption},
end

/-- Lemma 9.7 of [Analytic]. -/
lemma lem97' (hΛ_tf : torsion_free Λ) [hΛ_fg : module.finite ℤ Λ]
  {ι : Type*} [fintype ι] (N : ℕ) (l : ι → Λ) :
  ∃ A : finset (Λ →+ ℤ), ∀ x : Λ →+ ℤ, ∃ (x' ∈ A) (y : Λ →+ ℤ),
    x = N • y + x' ∧
    ∀ i, (x (l i)).nat_abs = N * (y (l i)).nat_abs + (x' (l i)).nat_abs :=
begin
  sorry
end
