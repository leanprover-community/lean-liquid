import category_theory.shift
import algebra.homology.homological_complex
import algebra.homology.homotopy_category
import data.int.parity
import tactic.ring
import category_theory.arrow
import category_theory.preadditive

local attribute [simp] category_theory.preadditive.zsmul_comp category_theory.preadditive.comp_zsmul


-- move this section
namespace int

def neg_one_pow (n : ℤ) : ℤ := @has_pow.pow (units ℤ) ℤ _ (-1) n

@[simp] lemma neg_one_pow_add (n m : ℤ) : neg_one_pow (n + m) = neg_one_pow n * neg_one_pow m :=
by { delta neg_one_pow, rw zpow_add, simp }

@[simp] lemma neg_one_pow_one : neg_one_pow 1 = -1 := rfl

-- This lemma is provable by `neg_one_pow_neg`, but it is nice to have a rfl-lemma for this.
-- The priority is thus higher to silence the linter.
@[simp, priority 1100] lemma neg_one_pow_neg_one : neg_one_pow (-1) = -1 := rfl

@[simp] lemma neg_one_pow_neg_zero : neg_one_pow 0 = 1 := rfl

lemma neg_one_pow_ite (n : ℤ) : neg_one_pow n = if even n then 1 else -1 :=
begin
  induction n using int.induction_on with n h n h,
  { simp [neg_one_pow] },
  { simp [h, apply_ite has_neg.neg] with parity_simps },
  { rw [sub_eq_add_neg, neg_one_pow_add],
    simp [h, apply_ite has_neg.neg] with parity_simps }
end

lemma neg_one_pow_even {n : ℤ} (h : even n) : neg_one_pow n = 1 :=
by rw [neg_one_pow_ite, if_pos h]

lemma neg_one_pow_odd {n : ℤ} (h : odd n) : neg_one_pow n = -1 :=
by rw [neg_one_pow_ite, if_neg (odd_iff_not_even.mp h)]

@[simp] lemma neg_one_pow_bit0 (n : ℤ) : neg_one_pow (bit0 n) = 1 :=
neg_one_pow_even (even_bit0 n)

@[simp] lemma neg_one_pow_bit1 (n : ℤ) : neg_one_pow (bit1 n) = -1 :=
neg_one_pow_odd (odd_bit1 n)

lemma neg_one_pow_eq_pow_abs (n : ℤ) : neg_one_pow n = (-1) ^ n.nat_abs :=
begin
  rw neg_one_pow_ite,
  convert (neg_one_pow_ite n.nat_abs).symm using 2,
  { simp with parity_simps },
  { delta neg_one_pow, simp }
end

lemma neg_one_pow_eq_neg_one_npow (n : ℕ) : neg_one_pow n = (-1) ^ n :=
by { delta neg_one_pow, simp }

@[simp] lemma neg_one_pow_neg (n : ℤ) : neg_one_pow (-n) = neg_one_pow n :=
by simp [neg_one_pow_ite] with parity_simps

@[simp] lemma neg_one_pow_sub (n m : ℤ) : neg_one_pow (n - m) = neg_one_pow n * neg_one_pow m :=
by rw [sub_eq_neg_add, neg_one_pow_add, neg_one_pow_neg, mul_comm]

@[simp] lemma neg_one_pow_mul_self (n : ℤ) : neg_one_pow n * neg_one_pow n = 1 :=
by { delta neg_one_pow, simp }

@[simp] lemma neg_one_pow_smul_self {α : Type*} [add_comm_group α] (n : ℤ) (X : α) :
  neg_one_pow n • neg_one_pow n • X = X :=
by simp [smul_smul]

open category_theory

variables {A : Type*} [category A] [preadditive A]

@[simps]
def neg_one_pow_smul_iso (n : ℤ) {X Y : A} (e : X ≅ Y) : X ≅ Y :=
{ hom := n.neg_one_pow • e.hom,
  inv := n.neg_one_pow • e.inv }

@[simps]
def neg_one_pow_arrow_iso_left (n : ℤ) {X Y : A} (f : X ⟶ Y) :
  arrow.mk f ≅ arrow.mk (n.neg_one_pow • f) :=
arrow.iso_mk (n.neg_one_pow_smul_iso (iso.refl _)) (iso.refl _) (by { dsimp, simp })

@[simps]
def neg_one_pow_arrow_iso_right (n : ℤ) {X Y : A} (f : X ⟶ Y) :
  arrow.mk f ≅ arrow.mk (n.neg_one_pow • f) :=
arrow.iso_mk (iso.refl _) (n.neg_one_pow_smul_iso (iso.refl _)) (by { dsimp, simp })

end int
