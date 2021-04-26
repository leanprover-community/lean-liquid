import polyhedral_lattice.basic
import for_mathlib.grading

/-

# Gordan's Lemma

We formalise the algebraic proof of Gordan's lemma on Wikipedia.
See also `src/toric/gordan_algebraic_blueprint.tex`; this should
perhaps go into the blueprint.

-/

-- solves a diamond

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

def dual_finset (S : finset Λ) : submodule ℕ (Λ →+ ℤ) :=
explicit_dual_set (coe : (S : set Λ) → Λ)

lemma dual_finset_antimono {S T : finset Λ} (hST : S ⊆ T) :
  dual_finset T ≤ dual_finset S :=
begin
  rintro φ hφ ⟨i, (his : i ∈ S)⟩,
  exact hφ ⟨i, hST his⟩,
end

lemma explicit_dual_set_eq_dual_finset [decidable_eq Λ] [fintype ι] (l : ι → Λ) :
  explicit_dual_set l = dual_finset (finset.image l finset.univ) :=
begin
  ext φ,
  split,
  { rintro hφ ⟨t, ht : t ∈ finset.image _ _⟩,
    rw finset.mem_image at ht,
    rcases ht with ⟨i, -, rfl⟩,
    exact hφ i },
  { rintro hφ i,
    refine hφ ⟨l i, (_ : l i ∈ finset.image _ _)⟩,
    rw finset.mem_image,
    exact ⟨i, finset.mem_univ _, rfl⟩ }
end

universe u
/-- The key inductive step in the proof of Gordan's Lemma -/
lemma Gordan_inductive_step (d : ℕ) {Λ : Type u}
  (hd : ∀ {{Γ : Type u}} (S : finset Γ) [add_comm_group Γ], by exactI ∀
        [module ℤ Γ], by exactI ∀
        (hΓ : finite_free Γ)
        [decidable_eq Γ], hΓ.rank = d → (dual_finset S).fg)
  [add_comm_group Λ]
  [module ℤ Λ]
  (hΛ : finite_free Λ)
  [decidable_eq Λ]
  (hl : hΛ.rank = d + 1)
  ⦃l : Λ⦄
  {S : finset Λ}
  (hfg : (dual_finset S).fg)
  (hl : ¬l = 0) :
  (dual_finset (insert l S)).fg :=
let L : (Λ →+ ℤ) →+ ℤ :=
{ to_fun := λ φ, φ l,
  map_zero' := rfl,
  map_add' := λ _ _, rfl } in
begin
  admit,
end

/-- A finset version of Gordan's Lemma. -/
lemma finset_Gordan [module ℤ Λ] (hΛ : finite_free Λ) [decidable_eq Λ] (S : finset Λ) :
  (dual_finset S).fg :=
begin
  -- We proceed by induction on the rank of Λ.
  suffices : ∀ n : ℕ, hΛ.rank = n → (dual_finset S).fg,
  { exact this _ rfl},
  intro n,
  unfreezingI {induction n with d hd generalizing Λ S},
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
    -- now induct on the finset
    apply S.induction_on; clear S,
    { convert finite_free.top_fg hΛ.dual,
      rw eq_top_iff,
      rintro φ - ⟨i, -, hi⟩ },
    { -- inductive step
      -- this is the main work in the proof.
      rintro l S - hfg,
      by_cases hl0 : l = 0,
      { convert hfg using 1,
        refine le_antisymm (dual_finset_antimono (S.subset_insert _)) _,
        rintro φ hφ ⟨i, (hilS : i ∈ insert l S)⟩,
        rw finset.mem_insert at hilS,
        rcases hilS with (rfl | hiS),
        { subst hl0,
          convert le_refl _,
          exact φ.map_zero },
        { refine hφ ⟨i, hiS⟩ } },
      { exact Gordan_inductive_step d @hd hΛ hl hfg hl0 } } }
end

/-- A fintype version of Gordan's Lemma. -/
lemma explicit_gordan [module ℤ Λ] (hΛ : finite_free Λ) [fintype ι] (l : ι → Λ) :
  (explicit_dual_set l).fg :=
begin
  classical,
  rw explicit_dual_set_eq_dual_finset,
  apply finset_Gordan hΛ,
end
