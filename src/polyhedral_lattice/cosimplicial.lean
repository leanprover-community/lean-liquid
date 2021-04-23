import rescale.polyhedral_lattice
import polyhedral_lattice.cech

import facts.nnreal

/-!
# The cosimplicial polyhedral lattice attached to `Λ → Λ'`

Let `Λ` be a polyhedral lattice, and let `0 < n` be a natural number.
Let `Λ' := rescale n (fin n →₀ Λ)` be the polyhedral lattice
that is the `n`-fold direct sum of `Λ` with itself,
endowed with the norm `∥(l₁, l₂, ..., lₙ)∥ = (∥l₁∥ + ∥l₂∥ + ... + ∥lₙ∥) / n`.

The diagonal embedding `Λ → Λ'` is a norm-nonincreasing map.
In this file we construct the Cech conerve of this map.
It is a cosimplicial object in the category `PolyhedralLattice`.

Concretely, but in pseudo-code:
it consists of the objects `Λ'^(m)` defined as `(Λ')^m/L`,
where `L` is the sublattice `Λ ⊗ {x : ℤ^m | ∑ x = 0}`.
-/

noncomputable theory

universe variables u

open_locale nnreal big_operators
open category_theory finsupp

namespace PolyhedralLattice

variables (Λ : PolyhedralLattice.{u}) (N : ℕ) [hN : fact (0 < N)]

include hN

def rescaled_power : PolyhedralLattice :=
@of (rescale N (fin N) →₀ Λ) $ @rescale.polyhedral_lattice N (fin N →₀ Λ) _ _

def diagonal_embedding : Λ ⟶ rescaled_power Λ N :=
{ to_fun := λ l, @rescale.of N (fin N →₀ Λ) $ ∑ i, single_add_hom i l,
  map_add' := λ l₁ l₂, by { simp only [add_monoid_hom.map_add, finset.sum_add_distrib], refl }, -- defeq abuse
  strict' := λ l,
  begin
    rw [rescale.norm_def, equiv.symm_apply_apply, norm_def, nnreal.coe_nat_cast,
      sum_eq_sum_fintype],
    swap, { intro, exact norm_zero },
    apply le_of_eq,
    rw div_eq_iff, swap,
    { norm_cast, exact hN.out.ne' },
    simp only [← apply_add_hom_apply, add_monoid_hom.map_sum],
    simp only [apply_add_hom_apply, single_add_hom_apply, single_apply],
    convert finset.sum_const (∥l∥ : ℝ),
    { ext i, simp only [finset.sum_ite_eq', finset.mem_univ, if_true] },
    rw [mul_comm, nsmul_eq_mul, finset.card_univ, fintype.card_fin],
  end }

def cosimplicial : simplex_category ⥤ PolyhedralLattice.{u} :=
Cech_conerve $ diagonal_embedding Λ N

open simplex_category

def cosimplicial_augmentation_map : Λ ⟶ (cosimplicial Λ N).obj (mk 0) :=
Cech_augmentation_map _

end PolyhedralLattice
