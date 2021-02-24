import algebra.group.basic
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

lemma le_or_le {α : Type*} [linear_order α] (a b : α) :
  a ≤ b ∨ b ≤ a :=
(le_or_lt a b).imp id le_of_lt

lemma abs_add_eq_add_abs_iff (a b : ℤ) :
  abs (a + b) = abs a + abs b ↔ (0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) :=
begin
  sorry
end

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

end lem97

open pseudo_normed_group


variables (Λ : Type*) (r' : ℝ≥0) (S : Type*)
variables [fintype S] [normed_group Λ] [polyhedral_lattice Λ]

section

variables {S}

-- move this
@[simps]
def Mbar.coeff (s : S) (n : ℕ) : Mbar r' S →+ ℤ :=
{ to_fun := λ x, x s n,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

variables {Λ r'}

def Mbar.mk_aux (x : Λ →+ Mbar r' S) (y : S → ℕ → Λ →+ ℤ)
  (h : ∀ s n l, (y s n l).nat_abs ≤ (x l s n).nat_abs) :
  Λ →+ Mbar r' S :=
add_monoid_hom.mk' (λ l,
{ to_fun := λ s n, y s n l,
  coeff_zero' := λ s,
  by simpa only [int.nat_abs_eq_zero, Mbar.coeff_zero, le_zero_iff, int.nat_abs_zero] using h s 0 l,
  summable' :=
  begin
    intro s,
    apply nnreal.summable_of_le _ ((x l).summable s),
    intro n,
    apply mul_le_mul' _ le_rfl,
    exact_mod_cast h s n l
  end }) $ λ l₁ l₂, by { ext s n, exact (y s n).map_add l₁ l₂ }

lemma needs_better_name {ι : Type} [fintype ι] (l : ι → Λ) (hl : generates_norm l)
  (x : Λ →+ Mbar r' S) (y : S → ℕ → Λ →+ ℤ)
  (h : ∀ s n i, (y s n (l i)).nat_abs ≤ (x (l i) s n).nat_abs)
  (s : S) (n : ℕ) (l : Λ) :
  ((y s n l).nat_abs ≤ (x l s n).nat_abs) :=
begin
  obtain ⟨d, hd, c, h1, h2⟩ := hl l,
  sorry
end

end

lemma lem98 [fact (r' < 1)] (N : ℕ) (hN : 0 < N) :
  ∃ d, ∀ c (x : Λ →+ Mbar r' S) (hx : x ∈ filtration (Λ →+ Mbar r' S) c),
    ∃ y : fin N → (Λ →+ Mbar r' S),
      (x = ∑ i, y i) ∧
      (∀ i, y i ∈ filtration (Λ →+ Mbar r' S) (c/N + d)) :=
begin
  classical,
  obtain ⟨ι, _ftι, l, hl⟩ := polyhedral_lattice.polyhedral Λ, resetI,
  obtain ⟨A, hA⟩ := lem97' Λ polyhedral_lattice.tf N l,
  let d := finset.univ.sup (λ i, ∑ a in A, (a (l i)).nat_abs),
  use d,
  intros c x hx,
  -- `x` is a homomorphism `Λ →+ Mbar r' S`
  -- we split it into pieces `Λ →+ ℤ` for all coefficients indexed by `s` and `n`
  let x' : S → ℕ → Λ →+ ℤ := λ s n, (Mbar.coeff r' s n).comp x,
  have := λ s n, hA (x' s n), clear hA,
  choose x₁' hx₁' x₀' hx₀' H using this,
  -- now we assemble `x₀' : S → ℕ → Λ →+ ℤ` into a homomorphism `Λ →+ Mbar r' S`
  let x₀ : Λ →+ Mbar r' S := Mbar.mk_aux x x₀' _, swap,
  { intros s n l',
    apply needs_better_name l hl x,
    intros s' n' i,
    specialize H s' n' i,
    refine le_trans (le_add_right _) H.symm.le,
    exact nat.le_mul_of_pos_left hN },
  let xₐ : (Λ →+ ℤ) → Mbar r' S := λ a,
  { to_fun := λ s n, if x₁' s n = a ∧ 0 < n then 1 else 0,
    coeff_zero' := λ s, by simp only [not_lt_zero', and_false, if_false],
    summable' :=
    begin
      intro s,
      have := (normed_ring.summable_geometric_of_norm_lt_1 (r' : ℝ) _), swap,
      { rwa nnreal.norm_eq },
      simp only [← nnreal.coe_pow, nnreal.summable_coe] at this,
      apply nnreal.summable_of_le _ this,
      intro n,
      refine (mul_le_mul' _ le_rfl).trans (one_mul _).le,
      split_ifs; simp
    end },
  sorry
end
