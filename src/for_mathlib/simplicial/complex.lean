import algebra.module.hom
import algebra.big_operators
import data.fintype.card

import for_mathlib.preadditive_category
import system_of_complexes.complex
import .augmented

namespace category_theory

variables {C : Type*} [category C] [preadditive C] (M : cosimplicial_object C)

namespace cosimplicial_object

open simplex_category finset add_monoid_hom category_theory.preadditive
open_locale simplicial big_operators

/-- The coboundary map in the alternating face map cochain complex. -/
def coboundary (n : ℕ) : M.obj [n] ⟶ M.obj [n+1] :=
∑ i : fin (n+2), (-1:ℤ)^(i:ℕ) • (M.map $ δ i)

lemma coboundary_zero : coboundary M 0 = (M.map $ δ 0) - (M.map $ δ 1) :=
begin
  simp only [coboundary, fin.sum_univ_succ, fin.default_eq_zero, fin.coe_zero, one_gsmul,
    fin.coe_succ, univ_unique, neg_gsmul, pow_one, fin.succ_zero_eq_one, sum_singleton,
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

/-- Make a cochain complex from a cosimplicial object. -/
def to_cocomplex : cochain_complex ℕ C := cochain_complex.mk'
(λ n, M.obj [n]) (λ n, M.coboundary n) M.coboundary_coboundary

/-- A functorial version of `to_cocomplex`. -/
def cocomplex : cosimplicial_object C ⥤ cochain_complex ℕ C :=
{ obj := to_cocomplex,
  map := λ M N f,
  { f := λ i, f.app _,
    comm := begin
      intros i j,
      dsimp [to_cocomplex],
      split_ifs, swap, { simp },
      subst h,
      simp only [category_theory.category.comp_id, category_theory.eq_to_hom_refl, coboundary,
        preadditive.sum_comp, preadditive.comp_sum, comp_gsmul, gsmul_comp, nat_trans.naturality],
    end } }

namespace augmented

/-- The objects defining the cochain complex associated to an augmented cosimplicial object. -/
@[nolint unused_arguments]
def to_cocomplex_obj (M : augmented C) : ℕ → C
| 0 := augmented.point.obj M
| (n+1) := (augmented.drop.obj M).obj [n]

/-- The boundary maps defining the cochain complex associated to an augmented cosimplicial object.-/
def to_cocomplex_d {M : augmented C} : Π (n : ℕ), to_cocomplex_obj M n ⟶ to_cocomplex_obj M (n+1)
| 0 := M.hom.app _
| (n+1) := (augmented.drop.obj M).coboundary _

/-- The cochain complex associated to an augmented cosimplicial object. -/
@[simps]
def to_cocomplex (M : augmented C) : cochain_complex ℕ C := cochain_complex.mk'
(to_cocomplex_obj M) to_cocomplex_d
begin
  rintros (_|_),
  { dsimp [to_cocomplex_d],
    erw [coboundary_zero, preadditive.comp_sub, sub_eq_zero,
      ← M.hom.naturality, ← M.hom.naturality],
    refl },
  { apply coboundary_coboundary }
end

/-- A functorial version of to_cocomplex. -/
def cocomplex : augmented C ⥤ cochain_complex ℕ C :=
{ obj := to_cocomplex,
  map := λ M N f,
  { f := λ i,
    match i with
    | 0 := point.map f
    | (n+1) := (drop.map f).app _
    end,
    comm := begin
      intros i j,
      dsimp [to_cocomplex],
      split_ifs, swap, { simp },
      subst h,
      cases i,
      { dsimp [to_cocomplex_d],
        simp only [to_cocomplex_d, category_theory.category.comp_id],
        erw [← nat_trans.comp_app, ← f.w],
        refl },
      { dsimp [to_cocomplex_d, coboundary],
        simp only [preadditive.sum_comp, preadditive.comp_sum, comp_gsmul, gsmul_comp,
          category.comp_id],
        apply finset.sum_congr rfl,
        intros i _,
        erw (drop.map f).naturality,
        refl }
    end },
  map_id' := λ M, by { ext (_|_), tidy },
  map_comp' := λ M N K f g, by { ext (_|_), tidy } }

end augmented

end cosimplicial_object

end category_theory
