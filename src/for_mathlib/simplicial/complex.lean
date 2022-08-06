import data.fintype.card
import algebra.module.hom
import algebra.big_operators.fin
import algebraic_topology.simplicial_object

import algebra.homology.homological_complex

namespace category_theory

variables {C : Type*} [category C] [preadditive C] (M : cosimplicial_object C)

namespace cosimplicial_object

open simplex_category finset add_monoid_hom category_theory.preadditive
open_locale simplicial big_operators

/-- The coboundary map in the alternating face map cochain complex. -/
def coboundary (n : ℕ) : M.obj [n] ⟶ M.obj [n+1] :=
∑ i : fin (n+2), (-1:ℤ)^(i:ℕ) • (M.δ i)

lemma coboundary_zero : coboundary M 0 = (M.δ 0) - (M.δ 1) :=
begin
  simp only [coboundary, fin.sum_univ_succ, fin.default_eq_zero, fin.coe_zero, one_zsmul,
    fin.coe_succ, univ_unique, neg_zsmul, pow_one, fin.succ_zero_eq_one, sum_singleton,
    pow_zero, sub_eq_add_neg]
end

@[reassoc]
lemma coboundary_coboundary (n : ℕ) : coboundary M n ≫ coboundary M (n+1) = 0 :=
begin
  let s : finset (fin (n+2) × fin (n+3)) := univ.filter (λ ij, (ij.2:ℕ) ≤ ij.1),
  calc coboundary M n ≫ coboundary M (n+1)
      = comp_hom (∑ (i:fin (n+2)), (-1:ℤ)^(i:ℕ) • (M.δ i))
                 (∑ (i:fin (n+3)), (-1:ℤ)^(i:ℕ) • (M.δ i)) : rfl
  ... = ∑ (i : fin (n+2)) (j : fin (n+3)), (-1:ℤ)^(i+j:ℕ) • ((M.δ i) ≫ (M.δ j)) : _
  ... = ∑ ij : fin (n+2) × fin (n+3), (-1:ℤ)^(ij.1+ij.2:ℕ) • ((M.δ ij.1) ≫ (M.δ ij.2)) :
        by rw [← univ_product_univ, sum_product]
  ... =   (∑ ij in s,  (-1:ℤ)^(ij.1+ij.2:ℕ) • ((M.δ ij.1) ≫ (M.δ ij.2)))
        + (∑ ij in sᶜ, (-1:ℤ)^(ij.1+ij.2:ℕ) • ((M.δ ij.1) ≫ (M.δ ij.2))) :
        by rw sum_add_sum_compl
  ... = 0 : _,
  { simp only [map_sum, map_zsmul, finset_sum_apply, smul_apply, smul_sum, pow_add, mul_smul],
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
    rw [δ_comp_δ], swap,
    { rwa ← fin.coe_fin_le },
    rw [← neg_zsmul],
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
def to_cocomplex : cochain_complex C ℕ := cochain_complex.of
(λ n, M.obj [n]) (λ n, M.coboundary n) M.coboundary_coboundary

/-- A functorial version of `to_cocomplex`. -/
def cocomplex : cosimplicial_object C ⥤ cochain_complex C ℕ :=
{ obj := to_cocomplex,
  map := λ M N f,
  { f := λ i, f.app _,
    comm' := begin
      rintro i j (rfl : i + 1 = j),
      dsimp [to_cocomplex, cochain_complex.of],
      simp only [if_pos rfl, category.comp_id, eq_to_hom_refl, coboundary, δ,
        preadditive.sum_comp, preadditive.comp_sum, comp_zsmul, zsmul_comp, nat_trans.naturality],
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
def to_cocomplex (M : augmented C) : cochain_complex C ℕ := cochain_complex.of
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
def cocomplex : augmented C ⥤ cochain_complex C ℕ :=
{ obj := to_cocomplex,
  map := λ M N f,
  { f := λ i,
    match i with
    | 0 := point.map f
    | (n+1) := (drop.map f).app _
    end,
    comm' := begin
      rintro i j (rfl : i + 1 = j),
      dsimp [to_cocomplex, cochain_complex.of],
      simp only [if_pos rfl, eq_to_hom_refl, category.comp_id],
      cases i,
      { dsimp [to_cocomplex_d],
        erw [← nat_trans.comp_app, ← f.w],
        refl },
      { dsimp [to_cocomplex_d, coboundary],
        simp only [preadditive.sum_comp, preadditive.comp_sum, comp_zsmul, zsmul_comp],
        apply fintype.sum_congr,
        intro i,
        erw (drop.map f).naturality,
        refl }
    end },
  map_id' := λ M, by { ext (_|_), tidy },
  map_comp' := λ M N K f g, by { ext (_|_), tidy } }

end augmented

end cosimplicial_object

end category_theory


namespace category_theory

variables {C : Type*} [category C] [preadditive C] (M : simplicial_object C)

namespace simplicial_object

open simplex_category finset category_theory.preadditive opposite
open_locale simplicial big_operators

/-- The boundary map in the alternating face map chain complex. -/
def boundary (n : ℕ) : M.obj (opposite.op [n+1]) ⟶ M.obj (opposite.op [n]) :=
∑ i : fin (n+2), (-1:ℤ)^(i:ℕ) • (M.δ i)

lemma boundary_zero : boundary M 0 = (M.δ 0) - (M.δ 1) :=
begin
  simp only [boundary, fin.sum_univ_succ, fin.default_eq_zero, fin.coe_zero, one_zsmul,
    fin.coe_succ, univ_unique, neg_zsmul, pow_one, fin.succ_zero_eq_one, sum_singleton,
    pow_zero, sub_eq_add_neg]
end

lemma coboundary_right_op (n : ℕ) :
  (cosimplicial_object.coboundary (M.right_op) n).unop = boundary M n :=
begin
  dsimp only [cosimplicial_object.coboundary, boundary],
  simp only [unop_sum, unop_zsmul],
  refl
end

@[reassoc]
lemma boundary_boundary (n : ℕ) : boundary M (n+1) ≫ boundary M n = 0 :=
begin
  rw [← coboundary_right_op, ← coboundary_right_op, ← unop_comp,
    cosimplicial_object.coboundary_coboundary, unop_zero],
end

/-- Make a chain complex from a simplicial object. -/
def to_complex : chain_complex C ℕ := chain_complex.of
(λ n, M.obj (opposite.op [n])) (λ n, M.boundary n) M.boundary_boundary

/-- A functorial version of `to_complex`. -/
def complex : simplicial_object C ⥤ chain_complex C ℕ :=
{ obj := to_complex,
  map := λ M N f,
  { f := λ i, f.app _,
    comm' := begin
      rintro i j (rfl : j + 1 = i),
      dsimp [to_complex, chain_complex.of],
      simp only [if_pos rfl, category.id_comp, eq_to_hom_refl, boundary, δ,
        preadditive.sum_comp, preadditive.comp_sum, comp_zsmul, zsmul_comp, nat_trans.naturality],
    end } }

namespace augmented

/-- The objects defining the chain complex associated to an augmented simplicial object. -/
@[nolint unused_arguments]
def to_complex_obj (M : augmented C) : ℕ → C
| 0 := augmented.point.obj M
| (n+1) := (augmented.drop.obj M).obj (opposite.op [n])

/-- The boundary maps defining the chain complex associated to an augmented simplicial object.-/
def to_complex_d {M : augmented C} : Π (n : ℕ), to_complex_obj M (n+1) ⟶ to_complex_obj M n
| 0 := M.hom.app _
| (n+1) := (augmented.drop.obj M).boundary _

/-- The chain complex associated to an augmented simplicial object. -/
@[simps]
def to_complex (M : augmented C) : chain_complex C ℕ := chain_complex.of
(to_complex_obj M) to_complex_d
begin
  rintros (_|_),
  { dsimp [to_complex_d],
    erw [boundary_zero, preadditive.sub_comp, sub_eq_zero,
      M.hom.naturality, M.hom.naturality],
    refl },
  { apply boundary_boundary }
end

/-- A functorial version of to_complex. -/
def complex : augmented C ⥤ chain_complex C ℕ :=
{ obj := to_complex,
  map := λ M N f,
  { f := λ i,
    match i with
    | 0 := point.map f
    | (n+1) := (drop.map f).app _
    end,
    comm' := begin
      rintro i j (rfl : j + 1 = i),
      dsimp [to_complex, chain_complex.of],
      simp only [if_pos rfl, eq_to_hom_refl, category.id_comp],
      cases j,
      { dsimp [to_complex_d],
        erw [← nat_trans.comp_app, f.w],
        refl },
      { dsimp [to_complex_d, boundary],
        simp only [preadditive.sum_comp, preadditive.comp_sum, comp_zsmul, zsmul_comp],
        apply fintype.sum_congr,
        intro i,
        erw (drop.map f).naturality,
        refl }
    end },
  map_id' := λ M, by { ext (_|_), tidy },
  map_comp' := λ M N K f g, by { ext (_|_), tidy } }

end augmented

end simplicial_object

end category_theory
