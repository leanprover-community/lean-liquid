import polyhedral_lattice.basic
import linear_algebra.dual
import for_mathlib.grading
import for_mathlib.nnrat
import for_mathlib.rational_cones

/-

# Gordan's Lemma

The algebraic proof of Gordan's lemma on Wikipedia.
See also `src/toric/gordan_algebraic_blueprint.tex`; this should
perhaps go into the LTE blueprint.

-/

universe u
variables {Λ : Type u} [add_comm_group Λ]
variable {ι : Type*}

open_locale big_operators
open_locale nnreal

def explicit_dual_set (l : ι → Λ) : submodule ℕ (Λ →+ ℤ) :=
{ carrier := {x | ∀ i, 0 ≤ x (l i)},
  zero_mem' := λ i, le_rfl,
  add_mem' := λ x y hx hy i, add_nonneg (hx i) (hy i),
  smul_mem' := λ n x hx i, nsmul_nonneg (hx i) n }

lemma mem_explicit_dual_set (l : ι → Λ) (x : Λ →+ ℤ) :
  x ∈ explicit_dual_set l ↔ ∀ i, 0 ≤ x (l i) := iff.rfl

def dual_finset (S : finset Λ) : submodule ℕ (Λ →+ ℤ) :=
explicit_dual_set (coe : (S : set Λ) → Λ)

lemma mem_dual_finset (S : finset Λ) (l : Λ →+ ℤ) :
  l ∈ dual_finset S ↔ ∀ x ∈ S, 0 ≤ l x :=
begin
  rw [dual_finset, mem_explicit_dual_set],
  simp
end

lemma dual_finset_antimono {S T : finset Λ} (hST : S ⊆ T) :
  dual_finset T ≤ dual_finset S :=
begin
  rintro φ hφ ⟨i, his : i ∈ S⟩,
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

lemma finset_Gordan_pi {α : Type*} [fintype α] (S : finset (α → ℤ)) :
  (dual_finset S).fg :=
begin
  sorry
end

def left_conj {F G : Type*}
  [add_comm_group F] [add_comm_group G]
  (e : F ≃ₗ[ℕ] G) :
  (F →+ ℤ) ≃ₗ[ℕ] (G →+ ℤ) :=
{ to_fun := λ f, f.comp e.symm.to_linear_map.to_add_monoid_hom,
  inv_fun := λ f, f.comp e.to_linear_map.to_add_monoid_hom,
  map_add' := λ f g,
  begin
    ext x,
    simp only [add_monoid_hom.coe_comp, function.comp_app, add_monoid_hom.add_apply],
  end,
  map_smul' := λ f r,
  begin
    ext x,
    refl,
  end,
  left_inv := λ f,
  begin
    ext x,
    simp,
  end,
  right_inv := λ f,
  begin
    ext x,
    simp,
  end }

/-- A finset version of Gordan's Lemma. -/
lemma finset_Gordan (hΛ : finite_free Λ) [decidable_eq Λ] (S : finset Λ) :
  (dual_finset S).fg :=
begin
  classical,
  let e := hΛ.is_basis.equiv_fun,
  obtain ⟨S', hS'⟩ := finset_Gordan_pi (S.image e),
  refine ⟨S'.image (λ f, f.comp e.to_linear_map.to_add_monoid_hom), _⟩,
  apply le_antisymm,
  { rw submodule.span_le,
    rintro f hf,
    simp only [set.mem_image, finset.mem_coe, finset.coe_image] at hf,
    rcases hf with ⟨φ, hφ, rfl⟩,
    rintro ⟨x, hx⟩,
    have : φ ∈ submodule.span ℕ (S' : set ((hΛ.basis_type → ℤ) →+ ℤ)),
    { apply submodule.subset_span,
      apply hφ },
    dsimp,
    rw hS' at this,
    apply this ⟨e x, _⟩,
    simp only [finset.mem_coe, finset.coe_image],
    refine ⟨_, hx, rfl⟩ },
  { intros x hx,
    rw finset.coe_image,


  }

  -- let t : (Λ →+ ℤ) ≃ₗ[ℤ] (hΛ.basis_type → ℤ) →+ ℤ := left_conj e',
  -- have q : dual_finset (finset.image ⇑e S) = (submodule.map e (dual_finset S)),
  -- { ext φ,
  --   simp only [mem_dual_finset, submodule.mem_map],
  --   simp only [and_imp, linear_map.coe_mk, finset.mem_image, forall_apply_eq_imp_iff₂,
  --     exists_imp_distrib],
  --   split,
  --   { intro h,
  --     refine ⟨⟨λ x, φ (e x), _, _⟩, h, _⟩,
  --     { simp only [linear_equiv.map_zero, add_monoid_hom.map_zero] },
  --     { intros x y, simp only [add_monoid_hom.map_add, linear_equiv.map_add], },
  --     { ext x,
  --       simp } },
  --   { rintro ⟨φ, hφ, rfl⟩,
  --     simpa only [add_monoid_hom.coe_comp, add_monoid_hom.coe_mk, function.comp_app,
  --       linear_equiv.symm_apply_apply] using hφ} },

  -- rw q at z,
  -- refine submodule.fg_of_fg_map t _,

  -- -- We proceed by induction on the rank of Λ.
  -- suffices : ∀ n : ℕ, hΛ.rank = n → (dual_finset S).fg,
  -- { exact this _ rfl},
  -- intro n,
  -- unfreezingI {induction n with d hd generalizing Λ S},
  -- { -- base case, rank of Λ = 0.
  --   intros hl,
  --   haveI hs := finite_free.rank_zero hl,
  --   use ∅,
  --   ext φ,
  --   have hφ : φ = 0,
  --   { ext l,
  --     convert φ.map_zero },
  --   subst hφ,
  --   simp },
  -- { -- inductive step, assume result for Λ of rank d, and deduce it for rank d+1
  --   rintro (hl : hΛ.rank = d + 1),
  --   -- now induct on the finset
  --   apply S.induction_on; clear S,
  --   { convert finite_free.top_fg hΛ.dual,
  --     rw eq_top_iff,
  --     rintro φ - ⟨i, -, hi⟩ },
  --   { -- inductive step
  --     -- this is the main work in the proof.
  --     rintro l S - hfg,
  --     by_cases hl0 : l = 0,
  --     { convert hfg using 1,
  --       refine le_antisymm (dual_finset_antimono (S.subset_insert _)) _,
  --       rintro φ hφ ⟨i, (hilS : i ∈ insert l S)⟩,
  --       rw finset.mem_insert at hilS,
  --       rcases hilS with (rfl | hiS),
  --       { subst hl0,
  --         convert le_refl _,
  --         exact φ.map_zero },
  --       { refine hφ ⟨i, hiS⟩ } },
  --     { -- We factor the hard work out into another lemma
  --       exact Gordan_inductive_step d @hd hΛ hl hfg hl0 } } }
end

/-- A fintype version of Gordan's Lemma. -/
lemma explicit_gordan [module ℤ Λ] (hΛ : finite_free Λ) [fintype ι] (l : ι → Λ) :
  (explicit_dual_set l).fg :=
begin
  classical,
  rw explicit_dual_set_eq_dual_finset,
  apply finset_Gordan hΛ,
end
