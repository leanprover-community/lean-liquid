import ring_theory.finiteness
/-!

# Finite free ℤ-modules

The basic theory of finite free ℤ-modules

## TODO

* rewrite to include multiplicative version
* also write version for modules, glue to version for groups
* Fill in `sorry`s (although Anne told kmb that they were bundling `is_basis` so
  I'm doing other things right now)
-/
def torsion_free (A : Type*) [add_comm_group A] : Prop :=
∀ (a : A) (ha : a ≠ 0) (n : ℕ), n • a = 0 → n = 0

-- TODO: multiplicative version
-- TODO: `is_basis` is being bundled by Anne so there's no point filling in proofs right now :-/

/-- `finite_free M` is the statement that the abelian group `M` is free of finite rank (over `ℤ`).-/
def finite_free (A : Type*) [add_comm_group A] : Prop :=
∃ (ι : Type) [fintype ι], nonempty (basis ι ℤ A)

namespace finite_free

variables {A : Type*} [add_comm_group A] (ha : finite_free A)

/-- If `ha : finite_free Λ` then `ha.basis_type` is the `ι` which indexes the basis
  `ha.basis : ι → Λ`. -/
def basis_type : Type := classical.some ha

noncomputable instance : fintype (basis_type ha) := classical.some $ classical.some_spec ha

/-- If `ha : finite_free Λ` then `ha.basis : ι → Λ` is the basis. Here `ι := ha.basis_type`. -/
noncomputable def basis : basis ha.basis_type ℤ A :=
(classical.some_spec $ classical.some_spec ha).some

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

theorem dual (ha : finite_free A) : finite_free (A →+ ℤ) :=
begin
  -- do this after is_basis refactor?
  sorry
end

/-- The rank of a finite free abelian group. -/
noncomputable def rank (ha : finite_free A) : ℕ := fintype.card ha.basis_type

variable {ha}

/-- A rank zero abelian group has at most one element (yeah I know...). -/
lemma rank_zero (h0 : ha.rank = 0) : subsingleton A := subsingleton.intro
begin
  -- do this after is_basis refactor?
  sorry
end

lemma rank_dual (ha : finite_free A) : ha.dual.rank = ha.rank :=
begin
  -- do this after is_basis refactor?
  sorry
end

lemma congr_iso {B : Type} [add_comm_group B] (hab : A ≃+ B) (ha : finite_free A) :
  finite_free B :=
begin
  -- do this after is_basis refactor?
  sorry
end

lemma rank_iso {B : Type} [add_comm_group B] (hab : A ≃+ B) (ha : finite_free A) :
  (congr_iso hab ha).rank = ha.rank :=
begin
  -- do this after is_basis refactor?
  sorry
end

theorem ker (ha : finite_free A) (φ : A →+ ℤ) : finite_free φ.ker :=
begin
  -- submodule of Noetherian Z-module is f.g.,
  -- submodule of torsion-free is torsion-free,
  -- f.g. torsion-free => free
  sorry
end

theorem rank_ker (ha : finite_free A) (φ : A →+ ℤ) (hφ : φ ≠ 0) :
  (ker ha φ).rank + 1 = ha.rank :=
begin
  -- I don't know the best way of doing this
  sorry
end

end finite_free
