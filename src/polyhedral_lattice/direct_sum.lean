import polyhedral_lattice.basic

import linear_algebra.direct_sum_module
import algebra.direct_sum

noncomputable theory

open_locale direct_sum big_operators classical

local attribute [-instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

namespace polyhedral_lattice

variables {ι : Type} [fintype ι] (Λ : ι → Type*)
variables [Π i, polyhedral_lattice (Λ i)]

instance : has_norm (⨁ i, Λ i) :=
⟨λ x, ∑ i, ∥x i∥⟩

lemma direct_sum_norm_def (x : ⨁ i, Λ i) : ∥x∥ = ∑ i, ∥x i∥ := rfl

instance : normed_group (⨁ i, Λ i) :=
normed_group.of_core _ $
{ norm_eq_zero_iff :=
  begin
    intros x,
    simp only [direct_sum_norm_def, ← coe_nnnorm, ← nnreal.coe_sum, finset.mem_univ,
      nnreal.coe_eq_zero, finset.sum_eq_zero_iff, nnnorm_eq_zero, forall_prop_of_true],
    split,
    { intro h, ext, rw direct_sum.zero_apply, apply h, },
    { rintro rfl, intro, rw direct_sum.zero_apply, }
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

instance : polyhedral_lattice (⨁ i, Λ i) :=
{ finite_free := sorry,
  polyhedral :=
  begin
    have := λ i, polyhedral_lattice.polyhedral (Λ i),
    choose J _instJ x hx using this, resetI,
    refine ⟨Σ i, J i, infer_instance, λ j, direct_sum.of _ j.1 (x _ j.2), _⟩,
    intro l,
    have := λ i, hx i (l i),
    choose d hd c H1 H2 using this,
    let d' : ι → ℕ := λ i₀, ∏ i in (finset.univ.erase i₀), d i,
    have hl : l = ∑ i, direct_sum.of _ i (l i),
    { sorry },
    refine ⟨∏ i, d i, _, λ j, d' j.1 * c j.1 j.2, _, _⟩,
    { apply nat.pos_of_ne_zero,
      rw finset.prod_ne_zero_iff,
      rintro i - hi,
      exact nat.not_lt_zero 0 (hi.subst $ hd i) },
    { rw [hl, finset.smul_sum, ← finset.univ_sigma_univ, finset.sum_sigma],
      apply fintype.sum_congr,
      intro i,
      rw [← finset.insert_erase (finset.mem_univ i), finset.prod_insert (finset.not_mem_erase _ _),
        mul_comm, mul_smul, ← nsmul_eq_smul (d i), ← add_monoid_hom.map_nsmul, nsmul_eq_smul, H1,
        add_monoid_hom.map_sum, finset.smul_sum],
      apply fintype.sum_congr,
      intro j,
      rw [mul_smul, ← nsmul_eq_smul (c i j), add_monoid_hom.map_nsmul, nsmul_eq_smul] },
    { rw [direct_sum_norm_def, ← finset.univ_sigma_univ, finset.sum_sigma, finset.mul_sum],
      apply fintype.sum_congr,
      intro i,
      dsimp,
      rw [← finset.insert_erase (finset.mem_univ i), finset.prod_insert (finset.not_mem_erase _ _),
        nat.cast_mul, mul_right_comm, H2],
      -- now use H2
      sorry }
  end }

end polyhedral_lattice
