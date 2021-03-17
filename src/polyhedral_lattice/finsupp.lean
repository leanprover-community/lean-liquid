import polyhedral_lattice.basic

import linear_algebra.finsupp_vector_space

noncomputable theory

open_locale big_operators classical

local attribute [-instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

namespace polyhedral_lattice

variables (ι : Type*) (Λ : Type*) [fintype ι] [polyhedral_lattice Λ]

instance : has_norm (ι →₀ Λ) := ⟨λ x, ∑ i, ∥x i∥⟩

lemma finsupp_norm_def (x : ι →₀ Λ) : ∥x∥ = ∑ i, ∥x i∥ := rfl

instance : normed_group (ι →₀ Λ) :=
normed_group.of_core _ $
{ norm_eq_zero_iff :=
  begin
    intros x,
    simp only [finsupp_norm_def, ← coe_nnnorm, ← nnreal.coe_sum, finset.mem_univ,
      nnreal.coe_eq_zero, finset.sum_eq_zero_iff, nnnorm_eq_zero, forall_prop_of_true,
      finsupp.ext_iff, finsupp.zero_apply],
  end,
  triangle :=
  begin
    intros x y,
    simp only [finsupp_norm_def, ← finset.sum_add_distrib, finsupp.add_apply],
    apply finset.sum_le_sum,
    rintro i -,
    apply norm_add_le,
  end,
  norm_neg := λ x, by simp only [finsupp_norm_def, norm_neg, finsupp.neg_apply] }

-- set_option pp.implicit true

instance {ι : Type} [fintype ι] : polyhedral_lattice (ι →₀ Λ) :=
{ finite_free :=
  begin
    obtain ⟨J, _instJ, l, hl⟩ := @polyhedral_lattice.finite_free Λ _, resetI,
    exact ⟨_, infer_instance, _, @finsupp.is_basis_single ℤ Λ ι _ _ _ _ (λ i, l) (λ i, hl)⟩
  end,
  polyhedral :=
  begin
    obtain ⟨J, _instJ, x, hx⟩ := polyhedral_lattice.polyhedral Λ, resetI,
    refine ⟨ι × J, infer_instance, λ j, finsupp.single j.1 (x j.2), _⟩,
    intro l,
    have := λ i, hx (l i),
    choose d hd c H1 H2 using this,
    let d' : ι → ℕ := λ i₀, ∏ i in (finset.univ.erase i₀), d i,
    have hl : l = ∑ i, finsupp.single i (l i),
    { conv_lhs { rw [← finsupp.sum_single l, finsupp.sum] },
      apply finset.sum_subset (finset.subset_univ _),
      rintro i - hi,
      rw finsupp.not_mem_support_iff at hi,
      rw [hi, finsupp.single_zero] },
    refine ⟨∏ i, d i, _, λ j, d' j.1 * c j.1 j.2, _, _⟩,
    { apply nat.pos_of_ne_zero,
      rw finset.prod_ne_zero_iff,
      rintro i - hi,
      exact nat.not_lt_zero 0 (hi.subst $ hd i) },
    { rw [hl, ← finset.univ_product_univ, finset.sum_product, finset.smul_sum],
      apply fintype.sum_congr,
      intro i,
      dsimp,
      simp only [mul_smul, ← finset.smul_sum],
      sorry },
    { rw [finsupp_norm_def, ← finset.univ_product_univ, finset.sum_product,
        finset.mul_sum],
      apply fintype.sum_congr,
      intro i,
      -- now use H2
      sorry }
  end }

end polyhedral_lattice
