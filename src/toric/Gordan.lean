import polyhedral_lattice.basic
import for_mathlib.grading

/-

# Gordan's Lemma

We formalise the
-/

variables {Λ : Type*} [add_comm_group Λ]
variable {ι : Type*}

open_locale big_operators


def explicit_dual_set (l : ι → Λ) : submodule ℕ (Λ →+ ℤ) :=
{ carrier := {x | ∀ i, 0 ≤ x (l i)},
  zero_mem' := λ i, le_rfl,
  add_mem' := λ x y hx hy i, add_nonneg (hx i) (hy i),
  smul_mem' := λ n x hx i,
    by { simp only [add_monoid_hom.coe_smul, pi.smul_apply], exact nsmul_nonneg (hx i) n } }

-- -- not sure we need this
-- lemma explicit_dual_set_of_neg (l : ι → Λ) (x : Λ →+ ℤ) :
--   x ∈ (explicit_dual_set (- l)) ↔ ∀ i, x (l i) ≤ 0 :=
-- begin
--   simp_rw [← neg_nonneg, ← add_monoid_hom.map_neg],
--   exact iff.rfl,
-- end

lemma explicit_gordan (hΛ : finite_free Λ) [fintype ι] (l : ι → Λ) :
  (explicit_dual_set l).fg :=
begin
  -- We proceed by induction on the rank of Λ.
  suffices : ∀ n : ℕ, hΛ.rank = n → (explicit_dual_set l).fg,
  { exact this _ rfl},
  intro n,
  tactic.unfreeze_local_instances,
  revert Λ ι,
  induction n with d hd,
  -- (There might be a slicker way to do that).
  { -- base case, rank of Λ = 0.
    sorry
  },
  { -- inductive step
    introsI Λ ι _inst_1 hΛ _inst_2 l,
    rintro (hl : hΛ.rank = d + 1),
    sorry
  }
end
