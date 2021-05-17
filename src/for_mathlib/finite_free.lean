import ring_theory.finiteness
import linear_algebra.invariant_basis_number
import linear_algebra.free_module
import linear_algebra.dual

/-!

# Finite free ℤ-modules

The basic theory of finite free ℤ-modules

## TODO

* rewrite to include multiplicative version
* also write version for modules, glue to version for groups
* Fill in `sorry`s
-/
def torsion_free (A : Type*) [add_comm_group A] : Prop :=
∀ (a : A) (ha : a ≠ 0) (n : ℕ), n • a = 0 → n = 0

-- TODO: multiplicative version

/-- `finite_free M` is the statement that the abelian group `M` is free of finite rank (over `ℤ`).-/
def finite_free (A : Type*) [add_comm_group A] : Prop :=
∃ (ι : Type) [fintype ι], nonempty (basis ι ℤ A)

section

example {A B : Type*} [add_comm_group A] [add_comm_group B] : module ℤ (A →ₗ[ℤ] B) := by refine linear_map.module

-- for mathlib, PR'd as #7629
@[simps]
def add_monoid_hom_lequiv_linear_map {A B : Type*} [add_comm_group A] [add_comm_group B] :
  (A →+ B) ≃ₗ[ℤ] (A →ₗ[ℤ] B) :=
{ to_fun := add_monoid_hom.to_int_linear_map,
  inv_fun := linear_map.to_add_monoid_hom,
  map_add' := by { intros, ext, refl },
  map_smul' := by { intros, ext, refl },
  left_inv := by { intros f, ext, refl },
  right_inv := by { intros f, ext, refl } }

end

namespace finite_free

variables {A : Type*} [add_comm_group A] (ha : finite_free A)

/-- If `ha : finite_free Λ` then `ha.basis_type` is the `ι` which indexes the basis
  `ha.basis : ι → Λ`. -/
def basis_type : Type := classical.some ha

noncomputable instance : fintype (basis_type ha) := classical.some $ classical.some_spec ha

/-- If `ha : finite_free Λ` then `ha.basis : ι → Λ` is the basis. Here `ι := ha.basis_type`. -/
noncomputable def basis : basis ha.basis_type ℤ A :=
(classical.some_spec $ classical.some_spec ha).some

noncomputable def its_basically_zn : A ≃ₗ[ℤ] (basis_type ha → ℤ) := ha.basis.equiv_fun

theorem top_fg (ha : finite_free A) : (⊤ : submodule ℕ A).fg :=
begin
  classical,
  use (finset.image (ha.basis) finset.univ) ∪ (finset.image (-ha.basis) finset.univ),
  rw eq_top_iff,
  rintro a -,
  rw ← ha.basis.total_repr a,
  generalize : (ha.basis.repr) a = f, clear a,
  apply finsupp.induction f; clear f,
  { exact submodule.zero_mem _ },
  { intros i z f hif hz hf,
    rw linear_map.map_add,
    refine submodule.add_mem _ _ hf,
    simp only [set.image_univ, finset.coe_union, pi.neg_apply, finsupp.total_single, linear_map.to_add_monoid_hom_coe,
      finset.coe_univ, finset.coe_image],
    -- next 6 lines -- what am I missing? I rewrite this twice later.
    have should_be_easy : ∀ (n : ℕ) (b : A), (n : ℤ) • b = n • b,
    { intros,
      induction n with n hn,
        simp,
      rw [nat.succ_eq_add_one, add_smul, ←hn],
      simp [add_smul] },
    let n := z.nat_abs,
    by_cases hz2 : z ≤ 0,
    -- nearly there
    { -- messy z≤0 case
      have hn2 : (n : ℤ) = - z := int.of_nat_nat_abs_of_nonpos hz2,
      rw [eq_neg_iff_eq_neg, ← mul_neg_one] at hn2,
      rw [hn2, mul_smul, neg_one_smul, should_be_easy],
      refine submodule.smul_mem _ n (submodule.subset_span (or.inr ⟨i, rfl⟩)) },
    { push_neg at hz2,
      rw [← int.of_nat_nat_abs_eq_of_nonneg (le_of_lt hz2)],
      change (n : ℤ) • _ ∈ _,
      rw should_be_easy,
      refine submodule.smul_mem _ n (submodule.subset_span (or.inl ⟨i, rfl⟩)) } },
end

-- def dual_basis_vecs (R : Type*) [comm_semiring R] (α : Type*) [fintype α] :
--   α → module.dual R (α → R) := linear_map.proj

-- lemma dual_basis_vecs_li (R : Type*) [comm_semiring R] (α : Type*) [fintype α] :
--   linear_independent R (dual_basis_vecs R α) :=
-- begin
--   rw fintype.linear_independent_iff,
--   intros g hg a,
--   classical,
--   let t : α → R := λ i, if i = a then 1 else 0,
--   have : (∑ (i : α), g i • dual_basis_vecs R α i) t = 0,
--   { rw hg,
--     simp },
--   simpa [dual_basis_vecs] using this,
-- end

-- lemma dual_basis_vecs_span (R : Type*) [comm_semiring R] (α : Type*) [fintype α] :
--   submodule.span R (set.range (dual_basis_vecs R α)) = ⊤ :=
-- begin
--   rw eq_top_iff,
--   rintro f -,
--   classical,
--   have : ∑ (i : α), f (pi.single i 1) • dual_basis_vecs R α i = f,
--   { ext x,
--     simp only [dual_basis_vecs, linear_map.coe_proj, algebra.id.smul_eq_mul, linear_map.smul_apply,
--       fintype.sum_apply, function.comp_app, linear_map.coe_fn_sum, function.eval_apply,
--       linear_map.coe_comp, linear_map.coe_single],
--     simp only [pi.single, function.update],
--     simp only [mul_boole, dite_eq_ite, eq_rec_constant, finset.mem_univ, if_true, pi.zero_apply,
--       finset.sum_ite_eq'] },
--   rw ←this,
--   refine submodule.sum_smul_mem _ _ _,
--   rintro c -,
--   apply submodule.subset_span,
--   simp
-- end


theorem dual (ha : finite_free A) : finite_free (A →+ ℤ) :=
begin
  rcases ha with ⟨ι, hι, ⟨b⟩⟩,
  refine ⟨ι, hι, ⟨_⟩⟩,
  classical,
  exact b.dual_basis.map add_monoid_hom_lequiv_linear_map.symm
end

/-- The rank of a finite free abelian group. -/
noncomputable def rank (ha : finite_free A) : ℕ := fintype.card ha.basis_type

-- move?
noncomputable
def equiv_fin {ι : Type*} [fintype ι] (b : _root_.basis ι ℤ A) :
  A ≃ₗ[ℤ] fin (fintype.card ι) → ℤ :=
(b.reindex (fintype.equiv_fin ι)).equiv_fun

lemma rank_eq {ι : Type*} [fintype ι] (b : _root_.basis ι ℤ A) (ha : finite_free A) :
  ha.rank = fintype.card ι :=
eq_of_fin_equiv ℤ $ (equiv_fin ha.basis).symm.trans (equiv_fin b)

noncomputable
def equiv_fin_rank (ha : finite_free A) :
  A ≃ₗ[ℤ] fin (ha.rank) → ℤ :=
equiv_fin (ha.basis)

variable {ha}

/-- A rank zero abelian group has at most one element (yeah I know...). -/
lemma rank_zero (h0 : ha.rank = 0) : subsingleton A :=
begin
  apply (ha.equiv_fin_rank).to_equiv.subsingleton_iff.mpr,
  rw h0,
  apply_instance,
end

lemma rank_dual (ha : finite_free A) : ha.dual.rank = ha.rank :=
begin
  have d := ha.dual,
  rcases ha with ⟨ι, hι, ⟨b⟩⟩,
  resetI, classical,
  exact (rank_eq (b.dual_basis.map add_monoid_hom_lequiv_linear_map.symm) d).trans
    (rank_eq b _).symm,
end

lemma congr_iso {B : Type} [add_comm_group B] (hab : A ≃+ B) (ha : finite_free A) :
  finite_free B :=
begin
  obtain ⟨ι, _, ⟨b⟩⟩ := ha,
  refine ⟨ι, ‹_›, ⟨b.map $ hab.to_linear_equiv _⟩⟩,
  intros n a,
  exact hab.to_add_monoid_hom.map_gsmul a n
end

lemma rank_iso {B : Type} [add_comm_group B] (hab : A ≃+ B) (ha : finite_free A) :
  (congr_iso hab ha).rank = ha.rank :=
begin
  apply eq_of_fin_equiv ℤ,
  refine (equiv_fin $ (congr_iso hab ha).basis).symm.trans _,
  refine (hab.symm.to_linear_equiv _).trans (equiv_fin ha.basis),
  intros n a,
  exact hab.symm.to_add_monoid_hom.map_gsmul a n
end

theorem ker (ha : finite_free A) (φ : A →+ ℤ) : finite_free φ.ker :=
begin
  obtain ⟨n, b⟩ := @module.free_of_finite_type_torsion_free' ℤ _ _ φ.ker _ _ (id _) (id _),
  { exact ⟨fin n, infer_instance, ⟨b⟩⟩ },
  { -- prove `module.finite R N` for `N : submodule R M` and Noetherian `M`.
    sorry },
  { -- prove this for arbitrary submodules
    sorry }
end

theorem rank_ker (ha : finite_free A) (φ : A →+ ℤ) (hφ : φ ≠ 0) :
  (ker ha φ).rank + 1 = ha.rank :=
begin
  -- I don't know the best way of doing this
  sorry
end

end finite_free
