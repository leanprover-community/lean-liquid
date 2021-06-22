import ring_theory.finiteness
import linear_algebra.free_module
import linear_algebra.dual

open_locale big_operators

variables (R M : Type*) [ring R] [add_comm_group M] [module R M]

lemma module.finite.of_basis {ι : Type*} [fintype ι] (b : basis ι R M) : module.finite R M :=
begin
  classical,
  refine ⟨⟨finset.univ.image b, _⟩⟩,
  simp only [set.image_univ, finset.coe_univ, finset.coe_image, basis.span_eq],
end

noncomputable
instance [nontrivial R] [module.finite R M] [module.free R M] :
  fintype (module.free.choose_basis_index R M) :=
begin
  classical,
  unfreezingI { obtain ⟨h⟩ := ‹module.finite R M› },
  choose s hs using h,
  let b := module.free.choose_basis R M,
  let t := (s.image b.repr).bUnion finsupp.support,
  refine { elems := t, complete := _ },
  intro i,
  by_contra hi,
  refine linear_dependent_iff.mpr _ b.linear_independent,
  rw [submodule.eq_top_iff'] at hs,
  specialize hs (b i),
  rw [finsupp.mem_span_iff_total] at hs,
  obtain ⟨c, hc⟩ := hs,
  let g := (∑ m : {x // x ∈ s}, c m • b.repr m) - finsupp.single i 1,
  have hgi : g i = -1,
  { rw [finsupp.sub_apply, finsupp.single_apply, if_pos rfl, finset.sum_apply', finset.sum_eq_zero,
      zero_sub],
    rintro j -,
    rw [finsupp.smul_apply],
    suffices : b.repr j i = 0, { rw [this, smul_zero] },
    rw [← finsupp.not_mem_support_iff],
    contrapose! hi,
    simp only [finset.mem_bUnion, exists_prop, finset.mem_image],
    exact ⟨_, ⟨j, j.2, rfl⟩, hi⟩, },
  refine ⟨insert i t, g, _, ⟨i, finset.mem_insert_self _ _, _⟩⟩,
  { rw [finset.sum_insert hi, hgi, neg_one_smul, neg_add_eq_zero],
    dsimp only [g],
    simp only [finsupp.sub_apply, sub_smul, finset.sum_sub_distrib],
    rw [eq_comm, sub_eq_iff_eq_add, eq_comm, finset.sum_eq_zero, add_zero],
    { simp only [finset.sum_apply', finset.sum_smul],
      rw [finset.sum_comm, ← hc, finsupp.total_apply, finsupp.sum_fintype],
      refine fintype.sum_congr _ _ _,
      { intro m,
        simp only [finsupp.smul_apply, smul_assoc, ← finset.smul_sum],
        congr' 1,
        convert (b.total_repr m).symm using 1, symmetry,
        apply finset.sum_subset,
        { intros x hx, rw finset.mem_bUnion,
          simp only [finset.mem_bUnion, exists_prop, finset.mem_image],
          exact ⟨_, ⟨_, m.2, rfl⟩, hx⟩, },
        { intros x hx1 hx2,
          rw [finsupp.not_mem_support_iff] at hx2,
          simp only [linear_map.smul_right_apply, linear_map.id_apply, hx2, zero_smul], } },
      { intro, exact zero_smul _ _ } },
    { intros j hj,
      rw [finsupp.single_apply, if_neg, zero_smul],
      rintro rfl, exact hi hj, } },
  { rw [hgi, ne.def, neg_eq_zero], exact one_ne_zero }
end

section
variables [module.finite ℤ M] [module.free ℤ M]

-- generalize?
instance : module.finite ℤ (M →+ ℤ) :=
begin
  classical,
  let b := module.free.choose_basis ℤ M,
  exact module.finite.of_basis ℤ _ (b.dual_basis.map add_monoid_hom_lequiv_int.symm),
end

-- generalize?
instance : module.free ℤ (M →+ ℤ) :=
begin
  classical,
  let b := module.free.choose_basis ℤ M,
  exact module.free.of_basis (b.dual_basis.map add_monoid_hom_lequiv_int.symm),
end

end
