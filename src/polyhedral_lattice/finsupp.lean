import polyhedral_lattice.basic

import linear_algebra.finsupp_vector_space

noncomputable theory

open_locale big_operators classical

local attribute [-instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

namespace finsupp

variables (ι : Type*) (Λ : Type*) [fintype ι]

section normed_group

variables [normed_group Λ]

instance : has_norm (ι →₀ Λ) := ⟨λ x, ∑ i, ∥x i∥⟩

lemma norm_def (x : ι →₀ Λ) : ∥x∥ = ∑ i, ∥x i∥ := rfl

@[simp] lemma norm_single (i : ι) (l : Λ) : ∥single i l∥ = ∥l∥ :=
begin
  simp only [norm_def, single_apply],
  rw finset.sum_eq_single i,
  { rw if_pos rfl },
  { intros _ j hj, rw [if_neg hj.symm, norm_zero], },
  { intro H, exact (H $ finset.mem_univ _).elim }
end

instance : normed_group (ι →₀ Λ) :=
normed_group.of_core _ $
{ norm_eq_zero_iff :=
  begin
    intros x,
    simp only [norm_def, ← coe_nnnorm, ← nnreal.coe_sum, finset.mem_univ,
      nnreal.coe_eq_zero, finset.sum_eq_zero_iff, nnnorm_eq_zero, forall_prop_of_true,
      finsupp.ext_iff, zero_apply],
  end,
  triangle :=
  begin
    intros x y,
    simp only [norm_def, ← finset.sum_add_distrib, add_apply],
    apply finset.sum_le_sum,
    rintro i -,
    apply norm_add_le,
  end,
  norm_neg := λ x, by simp only [norm_def, norm_neg, neg_apply] }

end normed_group

variables [polyhedral_lattice Λ]

instance {ι : Type} [fintype ι] : polyhedral_lattice (ι →₀ Λ) :=
{ finite_free :=
  begin
    obtain ⟨J, _instJ, l, hl⟩ := @polyhedral_lattice.finite_free Λ _, resetI,
    exact ⟨_, infer_instance, _, @is_basis_single ℤ Λ ι _ _ _ _ (λ i, l) (λ i, hl)⟩
  end,
  polyhedral :=
  begin
    obtain ⟨J, _instJ, x, hx⟩ := polyhedral_lattice.polyhedral Λ, resetI,
    refine ⟨ι × J, infer_instance, λ j, single j.1 (x j.2), _⟩,
    intro l,
    have := λ i, hx (l i),
    choose d hd c H1 H2 using this,
    let d' : ι → ℕ := λ i₀, ∏ i in (finset.univ.erase i₀), d i,
    have hl : l = ∑ i, single i (l i),
    { conv_lhs { rw [← sum_single l, sum] },
      apply finset.sum_subset (finset.subset_univ _),
      rintro i - hi,
      rw not_mem_support_iff at hi,
      rw [hi, single_zero] },
    refine ⟨∏ i, d i, _, λ j, d' j.1 * c j.1 j.2, _, _⟩,
    { apply nat.pos_of_ne_zero,
      rw finset.prod_ne_zero_iff,
      rintro i - hi,
      exact nat.not_lt_zero 0 (hi.subst $ hd i) },
    { rw [hl, ← finset.univ_product_univ, finset.sum_product, finset.smul_sum],
      apply fintype.sum_congr,
      intro i,
      rw [← finset.insert_erase (finset.mem_univ i), finset.prod_insert (finset.not_mem_erase _ _),
        mul_comm, mul_smul, ← nsmul_eq_smul (d i), ← single_add_hom_apply,
        ← add_monoid_hom.map_nsmul, nsmul_eq_smul, H1,
        add_monoid_hom.map_sum, finset.smul_sum],
      apply fintype.sum_congr,
      intro j,
      rw [mul_smul, ← nsmul_eq_smul (c i j), add_monoid_hom.map_nsmul, nsmul_eq_smul],
      refl },
    { rw [norm_def, ← finset.univ_product_univ, finset.sum_product,
        finset.mul_sum],
      apply fintype.sum_congr,
      intro i,
      dsimp,
      rw [← finset.insert_erase (finset.mem_univ i), finset.prod_insert (finset.not_mem_erase _ _),
        nat.cast_mul, mul_right_comm, H2, mul_comm, finset.mul_sum],
      apply fintype.sum_congr,
      intro j,
      rw [nat.cast_mul, mul_assoc, norm_single] }
  end }

end finsupp
