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
  unfreezingI {induction n with d hd generalizing Λ ι},
  -- (There might be a slicker way to do that).
  { -- base case, rank of Λ = 0.
    intros hl,
    haveI hs := finite_free.rank_zero hl,
    use ∅,
    ext φ,
    have hφ : φ = 0,
    { ext l,
      convert φ.map_zero },
    subst hφ,
    simp },
  { -- inductive step, assume result for Λ of rank d, and deduce it for rank d+1
    rintro (hl : hΛ.rank = d + 1),
    suffices : ∀ n : ℕ, fintype.card ι = n → (explicit_dual_set l).fg,
    { exact this _ rfl},
    -- Second induction, this time on size of ι.
    intro n,
    unfreezingI {induction n with d hd generalizing l ι},
    { -- base case, ι empty
      -- this is going to be `top_fg` in `polyhedral_lattice.basic`
      intro hι,
--      convert hΛ.top_fg,
      sorry
    },
    { -- inductive step
    sorry } }
end
