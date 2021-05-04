import algebraic_topology.simplicial_object
import algebra.module.hom
import algebra.big_operators

import for_mathlib.preadditive_category

import system_of_complexes.complex

/-! # The cochain complex of an augmented cosimplicial object in a preadditive category -/

universe variables u

open category_theory opposite simplex_category category_theory.preadditive
open add_monoid_hom finset

open_locale big_operators

variables {C : Type*} [category C] [preadditive C]
variables (X : C) (M : simplex_category ⥤ C) (f : X ⟶ M.obj (mk 0))

namespace alt_face_map_cocomplex

def coboundary (n : ℕ) :
  M.obj (mk n) ⟶ M.obj (mk $ n+1) :=
∑ i : fin (n+2), (-1:ℤ)^(i:ℕ) • (M.map $ δ i)

lemma coboundary_zero :
  coboundary M 0 = (M.map $ δ 0) - (M.map $ δ 1) :=
begin
  simp only [coboundary, fin.sum_univ_succ, fin.default_eq_zero, fin.coe_zero, one_smul,
    fin.coe_succ, univ_unique, neg_smul, pow_one, fin.succ_zero_eq_one, sum_singleton,
    pow_zero, sub_eq_add_neg]
end

@[reassoc]
lemma coboundary_coboundary (n : ℕ) : coboundary M n ≫ coboundary M (n+1) = 0 :=
begin
  let s : finset (fin (n+2) × fin (n+3)) := univ.filter (λ ij, (ij.2:ℕ) ≤ ij.1),
  calc coboundary M n ≫ coboundary M (n+1)
      = comp_hom (∑ (i:fin (n+2)), (-1:ℤ)^(i:ℕ) • (M.map $ δ i))
                 (∑ (i:fin (n+3)), (-1:ℤ)^(i:ℕ) • (M.map $ δ i)) : rfl
  ... = ∑ (i : fin (n+2)) (j : fin (n+3)), (-1:ℤ)^(i+j:ℕ) • ((M.map $ δ i) ≫ (M.map $ δ j)) : _
  ... = ∑ ij : fin (n+2) × fin (n+3), (-1:ℤ)^(ij.1+ij.2:ℕ) • ((M.map $ δ ij.1) ≫ (M.map $ δ ij.2)) :
        by rw [← univ_product_univ, sum_product]
  ... =   (∑ ij in s,  (-1:ℤ)^(ij.1+ij.2:ℕ) • ((M.map $ δ ij.1) ≫ (M.map $ δ ij.2)))
        + (∑ ij in sᶜ, (-1:ℤ)^(ij.1+ij.2:ℕ) • ((M.map $ δ ij.1) ≫ (M.map $ δ ij.2))) :
        by rw sum_add_sum_compl
  ... = 0 : _,
  { simp only [map_sum, map_gsmul, finset_sum_apply, smul_apply, smul_sum, pow_add, mul_smul],
    refl, },
  erw [← eq_neg_iff_add_eq_zero, ← finset.sum_neg_distrib],
  -- The sums are equal because we can give a bijection
  -- between the indexing sets, such that corresponding terms are equal.
  -- We get 4 goals. All the substance is in the second goal.
  refine (finset.sum_bij (λ (ij : fin (n+2) × fin (n+3)) hij,
    (ij.2.cast_lt (lt_of_le_of_lt (mem_filter.mp hij).right ij.1.is_lt), ij.1.succ))
    _ _ _ _),
  { -- Show that our function is well-defined
    rintro ⟨i,j⟩ hij, simp only [mem_filter, true_and, mem_univ, not_le, mem_compl, fin.coe_succ],
    dsimp [s] at hij ⊢, simp only [true_and, mem_filter, mem_univ] at hij,
    apply nat.lt_of_succ_le, apply nat.succ_le_succ, exact hij, },
  { -- The core of the proof.
    -- After all, we have to use the simplicial identity somewhere.
    rintros ⟨i,j⟩ hij_aux,
    have hij := (mem_filter.mp hij_aux).2,
    dsimp at hij ⊢,
    simp only [← M.map_comp],
    rw [δ_comp_δ], swap,
    { rwa ← fin.coe_fin_le },
    rw [← neg_gsmul],
    congr' 1,
    calc (-1) ^ (i + j : ℕ)
        = - (-1) ^ (i + j + 1 : ℕ) : _
    ... = - (-1) ^ (j + (i + 1) : ℕ) : _
    ... = _ : _,
    { rw [pow_succ, neg_one_mul, neg_neg] },
    { rw [add_assoc, add_left_comm] },
    { simp only [fin.coe_succ] } },
  { -- Show that our function is injective
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hij₁ hij₂ h,
    rw [prod.mk.inj_iff, fin.eq_iff_veq, fin.eq_iff_veq] at h ⊢,
    simp at h,
    rwa [and_comm] at h, },
  { -- Show that our function is surjective
    rintro ⟨i,j⟩ hij,
    refine ⟨⟨j.pred _, i.cast_succ⟩, _, _⟩,
    { intro H,
      rw [H, mem_compl, mem_filter, not_and] at hij,
      exact hij (mem_univ _) (nat.zero_le _) },
    { cases i,
      simp only [true_and, mem_compl, mem_filter, mem_univ, not_le, fin.coe_pred] at hij ⊢,
      exact nat.le_pred_of_lt hij, },
    { ext; simp only [fin.succ_pred, fin.pred_succ, fin.cast_lt_cast_succ], }, },
end

def obj : ℕ → C
| 0     := X
| (n+1) := M.obj (mk $ n)

variables {X M}

def d : Π n, obj X M n ⟶ obj X M (n+1)
| 0     := f
| (n+1) := coboundary M n

lemma d_comp_d (hf : f ≫ M.map (δ 0) = f ≫ M.map (δ 1)) : ∀ n, d f n ≫ d f (n+1) = 0
| 0     := show f ≫ coboundary M 0 = 0, by rw [coboundary_zero, comp_sub, hf, sub_self]
| (n+1) := coboundary_coboundary M n

end alt_face_map_cocomplex

variables {X M}

/-- The cochain complex of an augmented cosimplicial object in a preadditive category -/
def alt_face_map_cocomplex (hf : f ≫ M.map (δ 0) = f ≫ M.map (δ 1)) :
  cochain_complex ℕ C :=
cochain_complex.mk'
  (alt_face_map_cocomplex.obj X M)
  (alt_face_map_cocomplex.d f)
  (alt_face_map_cocomplex.d_comp_d f hf)
