import polyhedral_lattice.basic

import linear_algebra.direct_sum_module
import algebra.direct_sum
/-!

# Direct sums of polyhedral lattices

A finite direct sum of polyhedral lattices is...a seminormed group.

## TODO

Find out why the unfinished proof that a finite direct sum of polyhedral lattices
is a polyhedral lattice has been commented out. Right now this file does not seem to
be used in the project at all.

-/
noncomputable theory

open_locale direct_sum big_operators classical

namespace polyhedral_lattice

variables {ι : Type} [fintype ι] (Λ : ι → Type*)
variables [Π i, polyhedral_lattice (Λ i)]

instance : has_norm (⨁ i, Λ i) :=
⟨λ x, ∑ i, ∥x i∥⟩

lemma direct_sum_norm_def (x : ⨁ i, Λ i) : ∥x∥ = ∑ i, ∥x i∥ := rfl

instance : semi_normed_group (⨁ i, Λ i) :=
semi_normed_group.of_core _ $
{ norm_zero :=
  begin
    simp only [direct_sum_norm_def, ← coe_nnnorm, ← nnreal.coe_sum, finset.mem_univ, nnnorm_zero,
      nnreal.coe_eq_zero, finset.sum_eq_zero_iff, forall_prop_of_true, direct_sum.zero_apply,
      eq_self_iff_true, imp_true_iff],
  end,
  triangle :=
  begin
    intros x y,
    simp only [direct_sum_norm_def, ← finset.sum_add_distrib, direct_sum.add_apply],
    apply finset.sum_le_sum,
    rintro i -,
    apply norm_add_le,
  end,
  norm_neg :=
  begin
    intro x,
    simp only [direct_sum_norm_def],
    apply finset.sum_congr rfl,
    rintro i -,
    rw ← norm_neg (x i),
    congr' 1,
    apply dfinsupp.neg_apply -- this is missing for direct_sum
  end }

-- === superseded by a version using `finsupp`, so no need to complete this

-- instance : polyhedral_lattice (⨁ i, Λ i) :=
-- { finite_free := by admit,
--   polyhedral :=
--   begin
--     have := λ i, polyhedral_lattice.polyhedral (Λ i),
--     choose J _instJ x hx using this, resetI,
--     refine ⟨Σ i, J i, infer_instance, λ j, direct_sum.of _ j.1 (x _ j.2), _⟩,
--     intro l,
--     have := λ i, hx i (l i),
--     choose d hd c H1 H2 using this,
--     let d' : ι → ℕ := λ i₀, ∏ i in (finset.univ.erase i₀), d i,
--     have hl : l = ∑ i, direct_sum.of _ i (l i),
--     { admit },
--     refine ⟨∏ i, d i, _, λ j, d' j.1 * c j.1 j.2, _, _⟩,
--     { apply nat.pos_of_ne_zero,
--       rw finset.prod_ne_zero_iff,
--       rintro i - hi,
--       exact nat.not_lt_zero 0 (hi.subst $ hd i) },
--     { rw [hl, finset.smul_sum, ← finset.univ_sigma_univ, finset.sum_sigma],
--       apply fintype.sum_congr,
--       intro i,
--       rw [← finset.insert_erase (finset.mem_univ i), finset.prod_insert (finset.not_mem_erase _ _),
--         mul_comm, mul_smul, ← nsmul_eq_smul (d i), ← add_monoid_hom.map_nsmul, nsmul_eq_smul, H1,
--         add_monoid_hom.map_sum, finset.smul_sum],
--       apply fintype.sum_congr,
--       intro j,
--       rw [mul_smul, ← nsmul_eq_smul (c i j), add_monoid_hom.map_nsmul, nsmul_eq_smul] },
--     { rw [direct_sum_norm_def, ← finset.univ_sigma_univ, finset.sum_sigma, finset.mul_sum],
--       apply fintype.sum_congr,
--       intro i,
--       dsimp,
--       rw [← finset.insert_erase (finset.mem_univ i), finset.prod_insert (finset.not_mem_erase _ _),
--         nat.cast_mul, mul_right_comm, H2],
--       -- now use H2
--       admit }
--   end }

end polyhedral_lattice
