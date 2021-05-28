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
of (rescale N $ fin N →₀ Λ)

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
.

lemma diagonal_embedding_apply (l : Λ) (i : fin N) :
  ((@rescale.of N ((fin N) →₀ Λ)).symm (Λ.diagonal_embedding N l) : fin N →₀ Λ) i = l :=
by simp only [diagonal_embedding, single_add_hom_apply, finset.sum_apply',
    polyhedral_lattice_hom.coe_mk, equiv.symm_apply_apply, finsupp.single_apply,
    finset.sum_ite_eq', finset.mem_univ, if_true]

def cosimplicial_lift {M : Type*} [add_comm_group M] (m : ℕ) (g₀ : Λ →+ M)
  (g : fin (m + 1) → (Λ.rescaled_power N →+ M))
  (hg : ∀ i l, (g i) (Λ.diagonal_embedding N l) = g₀ l) :
  polyhedral_lattice.conerve.obj (Λ.diagonal_embedding N) (m + 1) →+ M :=
polyhedral_lattice.conerve.lift' _ m g₀ g hg $
begin
  intros l₁ l₂ h,
  rw [finsupp.ext_iff] at h,
  specialize h ⟨0, fact.out _⟩,
  erw [diagonal_embedding_apply, diagonal_embedding_apply] at h,
  exact h
end

lemma gsmul_rescaled_power (n : ℤ) (l : Λ.rescaled_power N) :
  n • (@rescale.of N ((fin N) →₀ Λ)).symm l = (@rescale.of N ((fin N) →₀ Λ)).symm (n • l) :=
rfl

instance : fact (polyhedral_lattice_hom.to_add_monoid_hom (Λ.diagonal_embedding N)).range.saturated :=
begin
  refine ⟨λ n l' h, _⟩,
  by_cases hn : n = 0, { exact or.inl hn },
  let l₀ : ↥Λ := ((@rescale.of N ((fin N) →₀ Λ)).symm l' : fin N →₀ Λ) ⟨0, hN.1⟩,
  refine or.inr ⟨l₀, _⟩,
  simp only [polyhedral_lattice_hom.coe_to_add_monoid_hom, add_monoid_hom.mem_range] at h ⊢,
  rw gsmul_eq_smul at h,
  obtain ⟨l, hl⟩ := h,
  refine @smul_left_injective ℤ _ _ _ _ _ n hn _ _ _, dsimp,
  rw [← hl, ← polyhedral_lattice_hom.map_gsmul],
  dsimp only [l₀],
  rw [← finsupp.smul_apply, gsmul_rescaled_power _ _ n l', ← hl, diagonal_embedding_apply],
end

def cosimplicial : cosimplicial_object PolyhedralLattice.{u} :=
Cech_conerve $ diagonal_embedding Λ N

open simplex_category

def cosimplicial_augmentation_map : Λ ⟶ (cosimplicial Λ N).obj (mk 0) :=
Cech_augmentation_map _

def augmented_cosimplicial : cosimplicial_object.augmented PolyhedralLattice.{u} :=
augmented_Cech_conerve $ diagonal_embedding Λ N

end PolyhedralLattice
