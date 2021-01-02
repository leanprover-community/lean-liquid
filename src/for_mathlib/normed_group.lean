import analysis.normed_space.basic

import normed_group_hom

noncomputable theory

open_locale nnreal

section

variables {V : Type*} [normed_group V]

lemma norm_nsmul_le (n : ℕ) (v : V) : ∥n •ℕ v∥ ≤ n * ∥v∥ :=
begin
  induction n with n ih,
  { simp only [norm_zero, nat.cast_zero, zero_mul, zero_nsmul] },
  { simp only [nat.succ_eq_add_one, add_nsmul, nat.cast_add,
      nat.cast_one, one_nsmul, add_mul, one_mul],
    calc ∥n •ℕ v + v∥
        ≤ ∥n •ℕ v∥ + ∥v∥ : norm_add_le _ _
    ... ≤ n * ∥v∥ + ∥v∥ : add_le_add_right ih _ }
end

lemma norm_gsmul_le (n : ℤ) (v : V) : ∥n •ℤ v∥ ≤ (abs n) * ∥v∥ :=
begin
  induction n,
  { simpa only [int.cast_coe_nat, int.of_nat_eq_coe, gsmul_coe_nat, nat.abs_cast]
      using norm_nsmul_le n v },
  { simpa only [gsmul_neg_succ_of_nat, abs_neg, norm_neg, int.cast_neg_succ_of_nat,
    ← nat.cast_add_one, nat.abs_cast] using norm_nsmul_le (n+1) v }
end

namespace normed_group

@[simps]
def nsmul (n : ℕ) : normed_group_hom V V :=
{ to_fun := λ v, n •ℕ v,
  map_zero' := nsmul_zero _,
  map_add' := λ _ _, nsmul_add _ _ _,
  bound' := ⟨n, λ v, norm_nsmul_le _ _⟩ }

lemma nsmul_bound_by (n : ℕ) : (nsmul n : normed_group_hom V V).bound_by n :=
λ v, by simpa only [nnreal.coe_nat_cast] using norm_nsmul_le n v

@[simps]
def gsmul (n : ℤ) : normed_group_hom V V :=
{ to_fun := λ v, n •ℤ v,
  map_zero' := gsmul_zero _,
  map_add' := λ _ _, gsmul_add _ _ _,
  bound' := ⟨abs n, λ v, norm_gsmul_le _ _⟩ }

lemma gsmul_bound_by (n : ℤ) : (gsmul n : normed_group_hom V V).bound_by (real.nnabs n) :=
norm_gsmul_le _

end normed_group

namespace normed_group_hom

open_locale big_operators nnreal

def mk_to_pi' {ι : Type} [fintype ι] (W : ι → Type*) [Π i, normed_group (W i)]
  (f : Π i, normed_group_hom V (W i)) (C : ι → ℝ≥0) (hC : ∀ i, (f i).bound_by (C i)) :
  normed_group_hom V (Π i, W i) :=
mk'
{ to_fun := λ v i, f i v,
  map_zero' := by { simp only [map_zero], refl },
  map_add' := by { intros, simp only [map_add], refl } }
(finset.sup finset.univ C)
begin
  intro v,
  rw pi_norm_le_iff (mul_nonneg (nnreal.coe_nonneg _) (norm_nonneg _)),
  intro i,
  calc ∥f i v∥ ≤ C i * ∥v∥ : (hC i) v
  ... ≤ _ * ∥v∥ : mul_le_mul _ le_rfl (norm_nonneg _) (nnreal.coe_nonneg _),
  rw nnreal.coe_le_coe,
  apply finset.le_sup (finset.mem_univ _)
end

lemma mk_to_pi'_bound_by {ι : Type} [fintype ι] (W : ι → Type*) [Π i, normed_group (W i)]
  (f : Π i, normed_group_hom V (W i)) (C : ι → ℝ≥0) (hC : ∀ i, (f i).bound_by (C i)) :
  (mk_to_pi' _ f C hC).bound_by (finset.sup finset.univ C) :=
mk'_bound_by _ _ _

def mk_to_pi {ι : Type} [fintype ι] (W : ι → Type*) [Π i, normed_group (W i)]
  (f : Π i, normed_group_hom V (W i)) : normed_group_hom V (Π i, W i) :=
mk_to_pi' _ f (λ i, classical.some (f i).bound) $ λ i, (classical.some_spec (f i).bound).2

def mk_from_pi' {ι : Type} [fintype ι] (V : ι → Type*) [Π i, normed_group (V i)]
  (W : Type*) [normed_group W] (f : Π i, normed_group_hom (V i) W)
  (C : ι → ℝ≥0) (hC : ∀ i, (f i).bound_by (C i)) :
  normed_group_hom (Π i, V i) W :=
mk'
{ to_fun := λ v, ∑ i, f i (v i),
  map_zero' := by { simp only [pi.zero_apply, map_zero, finset.sum_const_zero] },
  map_add' := by { intros, simp only [pi.add_apply, map_add, finset.sum_add_distrib] } }
(∑ i, C i)
begin
  intro v,
  calc ∥∑ i, f i (v i)∥ ≤ ∑ i, ∥f i (v i)∥ : norm_sum_le _ _
  ... ≤ ∑ i, C i * ∥v∥ : finset.sum_le_sum _ -- proven below
  ... = (∑ i, C i) * ∥v∥ : by rw finset.sum_mul
  ... = ↑(∑ i, C i) * ∥v∥ : by rw nnreal.coe_sum,
  rintro i -,
  calc ∥f i (v i)∥ ≤ C i * ∥v i∥ : (hC i) _
  ... ≤ C i * ∥v∥ : mul_le_mul le_rfl (norm_le_pi_norm _ _) (norm_nonneg _) (C i).coe_nonneg
end

def mk_from_pi'_bound_by {ι : Type} [fintype ι] (V : ι → Type*) [Π i, normed_group (V i)]
  (W : Type*) [normed_group W] (f : Π i, normed_group_hom (V i) W)
  (C : ι → ℝ≥0) (hC : ∀ i, (f i).bound_by (C i)) :
  (mk_from_pi' _ _ f C hC).bound_by (∑ i, C i) :=
mk'_bound_by _ _ _

def mk_from_pi {ι : Type} [fintype ι] (V : ι → Type*) [Π i, normed_group (V i)]
  (W : Type*) [normed_group W] (f : Π i, normed_group_hom (V i) W) :
  normed_group_hom (Π i, V i) W :=
mk_from_pi' _ _ f (λ i, classical.some (f i).bound) $ λ i, (classical.some_spec (f i).bound).2

end normed_group_hom

end
