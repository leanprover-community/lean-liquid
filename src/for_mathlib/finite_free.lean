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
def add_monoid_hom_lequiv_int {A B : Type*} [add_comm_group A] [add_comm_group B] :
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

noncomputable def its_basically_zn : A ≃ₗ[ℤ] (ha.basis_type → ℤ) := ha.basis.equiv_fun

lemma zn_finite {ι : Type*} [fintype ι] : module.finite ℤ (ι →₀ ℤ) :=
begin
  classical,
  rw [module.finite_def, submodule.fg_def],
  refine ⟨((λ i, finsupp.single i 1) '' set.univ),
    set.finite.image (λ (i : ι), finsupp.single i 1) set.finite_univ, _⟩,
  rw [← finsupp.supported_eq_span_single, finsupp.supported_univ]
end

lemma zn_finite' {ι : Type*} [fintype ι] : module.finite ℤ (ι → ℤ) :=
begin
  letI : module.finite ℤ (ι →₀ ℤ) := zn_finite,
  exact module.finite.equiv (finsupp.linear_equiv_fun_on_fintype ℤ)
end

lemma finite_free.finite (ha : finite_free A) : module.finite ℤ A :=
begin
  letI : module.finite ℤ (ha.basis_type → ℤ) := zn_finite',
  exact module.finite.equiv (its_basically_zn ha).symm,
end

theorem top_fg (ha : finite_free A) : (⊤ : submodule ℕ A).fg :=
begin
  have h₁ : (⊤ : submodule ℕ A).to_add_submonoid = (⊤ : add_subgroup A).to_add_submonoid := rfl,
  have h₂ : (⊤ : add_subgroup A) = (⊤ : submodule ℤ A).to_add_subgroup := rfl,
  rw [submodule.fg_iff_add_submonoid_fg, h₁, ← add_subgroup.fg_iff_add_submonoid.fg, h₂,
    ← submodule.fg_iff_add_subgroup_fg, ← module.finite_def],
  exact finite_free.finite ha
end

theorem dual (ha : finite_free A) : finite_free (A →+ ℤ) :=
begin
  rcases ha with ⟨ι, hι, ⟨b⟩⟩,
  refine ⟨ι, hι, ⟨_⟩⟩,
  classical,
  exact b.dual_basis.map add_monoid_hom_lequiv_int.symm
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
  exact (rank_eq (b.dual_basis.map add_monoid_hom_lequiv_int.symm) d).trans
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

end finite_free
