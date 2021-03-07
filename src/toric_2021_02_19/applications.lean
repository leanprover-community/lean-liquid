import toric_2021_02_19.toric
import data.real.nnreal

open_locale nnreal
open submodule pairing

variables {M : Type*} [add_comm_group M]
/-  This lemma is an application of `pointed_of_is_basis_is_inj`: it is present just as a proof
of concept that `pointed_of_is_basis_is_inj` applies in this case. -/
lemma pointed_nnR {R : Type*} [ordered_comm_ring R] [module R M] [semimodule (nnR R) M]
  [is_scalar_tower (nnR R) R M] {ι : Type*} {v : ι → M} (bv : is_basis R v) :
  pointed R (submodule.span (nnR R) (set.range v)) :=
pointed_of_is_basis_is_inj bv (is_inj_nonneg.nnR_ocr R)

/-  This lemma is an application of `pointed_of_is_basis_is_inj`: it is present just as a proof
of concept that `pointed_of_is_basis_is_inj` applies in this case. -/
lemma pointed_of_integers {ι : Type*} {v : ι → M} (bv : is_basis ℤ v) :
  pointed ℤ (submodule.span ℕ (set.range v)) :=
pointed_of_is_basis_is_inj bv (is_inj_nonneg.nat ℤ)

/-  This lemma is an application of `pointed_of_is_basis_is_inj`: it is present just as a proof
of concept that `pointed_of_is_basis_is_inj` applies in this case. -/
lemma pointed_of_rational {ι : Type*} {v : ι → M} [module ℚ M] (bv : is_basis ℚ v) :
  pointed ℚ (submodule.span ℕ (set.range v)) :=
pointed_of_is_basis_is_inj bv (is_inj_nonneg.nat ℚ)

/-  This lemma is an application of `pointed_of_is_basis_is_inj`: it is present just as a proof
of concept that `pointed_of_is_basis_is_inj` applies in this case. -/
lemma pointed_of_nat {R ι : Type*} [ordered_comm_ring R] [nontrivial R] [module R M] {v : ι → M}
  (bv : is_basis R v) :
  pointed R (submodule.span ℕ (set.range v)) :=
pointed_of_is_basis_is_inj bv (is_inj_nonneg.nat R)

instance : algebra ℝ≥0 ℝ := nnreal.to_real_hom.to_algebra

/-
variables {N : Type*} [add_comm_monoid N]

def semimodule.of_algebra (R S : Type*) [comm_semiring R] [semiring S] [algebra R S]
  [semimodule S N] :
  semimodule R N :=
{ smul := λ a b, algebra_map R S a • b,
  one_smul := λ a, by simp only [one_smul, ring_hom.map_one],
  mul_smul := λ x y m, by simp [(•), mul_smul ((algebra_map R S) x) ((algebra_map R S) y) m],
  smul_add := λ r m n, smul_add ((algebra_map R S) r) m n,
  smul_zero := λ r, smul_zero ((algebra_map R S) r),
  add_smul := λ a b m, by simp [(•), add_smul ((algebra_map R S) a) ((algebra_map R S) b) m],
  zero_smul := λ m, by simp only [ring_hom.map_zero, zero_smul] }

instance [semimodule ℝ N] : semimodule ℝ≥0 N := semimodule.of_algebra ℝ≥0 ℝ

instance ist [semimodule ℝ N] : is_scalar_tower ℝ≥0 ℝ N :=
{ smul_assoc := λ a b c, show (a.val • b) • c = a • b • c, by { rw smul_assoc a.val b c, congr } }
-/

/--  Without the instance `ist`, the proof below does not work. -/
lemma pointed_of_nnreal {ι : Type*} [module ℝ M] [semimodule ℝ≥0 M] [is_scalar_tower ℝ≥0 ℝ M]
  {v : ι → M} (bv : is_basis ℝ v) :
  pointed ℝ (submodule.span ℝ≥0 (set.range v)) :=
pointed_of_is_basis_is_inj bv (is_inj_nonneg.nnR_ocr ℝ)
