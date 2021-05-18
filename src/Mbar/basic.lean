import data.real.basic
import algebra.big_operators.basic
import topology.algebra.infinite_sum
import data.finset.basic
import data.equiv.basic
import analysis.normed_space.basic
import analysis.specific_limits
import data.equiv.basic

import Mbar.bounded
import pseudo_normed_group.basic

import for_mathlib.coe_nat_abs
import for_mathlib.tsum

/-!

## $\overline{\mathcal{M}}_{r'}(S)$

This file contains a definition of ℳ-barᵣ'(S) as defined at the very beginning
of section 9 of `analytic.pdf` (p57), and its action of `T⁻¹`.

## Implementation issues

We model Tℤ[[T]] as functions ℕ → ℤ which vanish at 0.

-/

universe u

noncomputable theory
open_locale big_operators nnreal

-- move this
lemma int.norm_def (n : ℤ) : ∥n∥ = abs n := rfl

section defs

set_option old_structure_cmd true

/-- `Mbar r' S` is the set of power series
`F_s = ∑ a_{s,n}T^n ∈ Tℤ[[T]]` such that `∑_{s,n} |a_{s,n}|r'^n` converges -/
structure Mbar (r' : ℝ≥0) (S : Type u) [fintype S] :=
(to_fun : S → ℕ → ℤ)
(coeff_zero' : ∀ s, to_fun s 0 = 0)
(summable' : ∀ s, summable (λ n, (↑(to_fun s n).nat_abs * r' ^ n)))

end defs

variables {r' : ℝ≥0} {S : Type u} [fintype S]

namespace Mbar

instance has_coe_to_fun : has_coe_to_fun (Mbar r' S) := ⟨_, Mbar.to_fun⟩

@[simp] lemma coe_mk (x h₁ h₂) : ((⟨x, h₁, h₂⟩ : Mbar r' S) : S → ℕ → ℤ) = x := rfl

@[simp] protected lemma coeff_zero (x : Mbar r' S) (s : S) : x s 0 = 0 := x.coeff_zero' s

protected lemma summable (x : Mbar r' S) (s : S) :
  summable (λ n, (↑(x s n).nat_abs * r' ^ n)) := x.summable' s

lemma summable_coe_real (x : Mbar r' S) (s : S) :
  summable (λ n, ∥x s n∥ * r' ^ n) :=
by simpa only [← nnreal.summable_coe, nnreal.coe_nat_cast, nnreal.coe_nat_abs,
  nnreal.coe_mul, nnreal.coe_pow] using x.summable s

@[ext] lemma ext (x y : Mbar r' S) (h : ⇑x = y) : x = y :=
by { cases x, cases y, congr, exact h }

lemma ext_iff (x y : Mbar r' S) : x = y ↔ (x : S → ℕ → ℤ) = y :=
⟨congr_arg _, ext x y⟩

/-- The zero element of `Mbar r' S`, defined as the constant 0-function. -/
def zero : Mbar r' S :=
{ to_fun := 0,
  coeff_zero' := λ s, rfl,
  summable' := λ s, by simpa using summable_zero }

/-- Addition in `Mbar r' S`, defined as pointwise addition. -/
def add (F : Mbar r' S) (G : Mbar r' S) : Mbar r' S :=
{ to_fun := F + G,
  coeff_zero' := λ s, by simp [F.coeff_zero s, G.coeff_zero s],
  summable' :=
  begin
    intro s,
    apply nnreal.summable_of_le _ ((F.summable s).add (G.summable s)),
    intro n,
    rw [← add_mul, ← nat.cast_add],
    apply mul_le_mul_right',
    rw nat.cast_le,
    exact int.nat_abs_add_le _ _
  end }

/-- Subtraction in `Mbar r' S`, defined as pointwise subtraction. -/
def sub (F : Mbar r' S) (G : Mbar r' S) : Mbar r' S :=
{ to_fun := F - G,
  coeff_zero' := λ s, by simp [F.coeff_zero s, G.coeff_zero s],
  summable' :=
  begin
    intro s,
    apply nnreal.summable_of_le _ ((F.summable s).add (G.summable s)),
    intro n,
    rw [← add_mul, ← nat.cast_add],
    apply mul_le_mul_right',
    rw [nat.cast_le, sub_eq_add_neg, ← int.nat_abs_neg (G s n)],
    -- there should be an `int.nat_abs_sub_le`
    exact int.nat_abs_add_le _ _
  end }

/-- Negation in `Mbar r' S`, defined as pointwise negation. -/
def neg (F : Mbar r' S) : Mbar r' S :=
{ to_fun := -F,
  coeff_zero' := λ s, by simp [F.coeff_zero s],
  summable' :=
  begin
    intro s,
    convert F.summable s using 1,
    ext n,
    simp only [pi.neg_apply, int.nat_abs_neg]
  end }

instance : has_zero (Mbar r' S) := ⟨zero⟩
instance : has_add (Mbar r' S) := ⟨add⟩
instance : has_sub (Mbar r' S) := ⟨sub⟩
instance : has_neg (Mbar r' S) := ⟨neg⟩

@[simp] lemma coe_zero : ⇑(0 : Mbar r' S) = 0 := rfl
@[simp] lemma coe_add (F G : Mbar r' S) : ⇑(F + G : Mbar r' S) = F + G := rfl
@[simp] lemma coe_sub (F G : Mbar r' S) : ⇑(F - G : Mbar r' S) = F - G := rfl
@[simp] lemma coe_neg (F : Mbar r' S) : ⇑(-F : Mbar r' S) = -F := rfl

/-- Tailored scalar multiplication by natural numbers. -/
def nsmul (N : ℕ) (F : Mbar r' S) : Mbar r' S :=
{ to_fun := λ s n, N • F s n,
  coeff_zero' := λ s, by simp only [F.coeff_zero, smul_zero],
  summable' := λ s,
  begin
    simp only [nsmul_eq_mul, int.nat_abs_mul, nat.cast_mul, mul_assoc, int.nat_abs_of_nat,
      int.nat_cast_eq_coe_nat, nnreal.coe_nat_abs],
    by_cases hN : N = 0,
    { simpa only [hN, nat.cast_zero, zero_mul] using summable_zero },
    simp only [← nnreal.summable_coe, nnreal.coe_mul],
    rw [← summable_mul_left_iff],
    { simp only [coe_nnnorm, nnreal.coe_nat_abs, nnreal.coe_pow], exact F.summable_coe_real s },
    { exact_mod_cast hN }
  end }

/-- Tailored scalar multiplication by integers. -/
def gsmul (N : ℤ) (F : Mbar r' S) : Mbar r' S :=
{ to_fun := λ s n, N • F s n,
  coeff_zero' := λ s, by simp only [F.coeff_zero, smul_zero],
  summable' := λ s,
  begin
    simp only [gsmul_eq_mul, int.nat_abs_mul, int.cast_id, nat.cast_mul, mul_assoc],
    by_cases hN : N.nat_abs = 0,
    { simpa only [hN, nat.cast_zero, zero_mul] using summable_zero },
    simp only [← nnreal.summable_coe, nnreal.coe_mul],
    rw [← summable_mul_left_iff],
    { simp only [coe_nnnorm, nnreal.coe_nat_abs, nnreal.coe_pow], exact F.summable_coe_real s },
    { exact_mod_cast hN }
  end }
.

instance : add_comm_group (Mbar r' S) :=
{ zero := 0, add := (+), sub := has_sub.sub, neg := has_neg.neg,
  zero_add := by { intros, ext, simp only [coe_zero, zero_add, coe_add] },
  add_zero := by { intros, ext, simp only [coe_zero, add_zero, coe_add] },
  add_assoc := by { intros, ext, simp only [add_assoc, coe_add] },
  add_left_neg := by { intros, ext,
    simp only [coe_add, coe_neg, coe_zero, pi.add_apply, pi.zero_apply, pi.neg_apply, add_left_neg] },
  add_comm := by { intros, ext, simp only [coe_add, add_comm] },
  sub_eq_add_neg := by { intros, ext, simp only [coe_sub, coe_add, coe_neg, sub_eq_add_neg] },
  nsmul := λ n F, F.nsmul n,
  nsmul_zero' := λ F, by { ext, simp only [nsmul, zero_smul], refl },
  nsmul_succ' := λ n F,
  begin
    ext,
    simp only [nsmul, nat.succ_eq_add_one, add_smul, one_smul, add_comm, coe_mk, coe_add,
      pi.add_apply],
  end,
  gsmul := λ n F, F.gsmul n,
  gsmul_zero' := λ F, by { ext, simp only [gsmul, zero_smul], refl },
  gsmul_succ' := λ n F,
  begin
    ext,
    simp only [gsmul, nat.succ_eq_add_one, algebra.id.smul_eq_mul, coe_mk, pi.add_apply,
      int.coe_nat_succ, int.of_nat_eq_coe, coe_add, add_mul, one_mul, add_comm],
  end,
  gsmul_neg' := λ n F,
  begin
    ext,
    simp only [gsmul, algebra.id.smul_eq_mul, coe_mk, pi.neg_apply, int.coe_nat_succ, coe_neg,
      add_mul, one_mul, neg_add_rev, int.neg_succ_of_nat_coe, neg_mul_eq_neg_mul_symm, one_mul],
  end }

/-- The `coeff s n` is the additive homomorphism that sends `x : Mbar r' S`
to the coefficient `x_{s,n}`. -/
@[simps]
def coeff (s : S) (n : ℕ) : Mbar r' S →+ ℤ :=
{ to_fun := λ x, x s n,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

/-- The norm of `F : Mbar r' S` as nonnegative real number.
It is defined as `∑ s, ∑' n, (↑(F s n).nat_abs * r' ^ n)`. -/
protected
def nnnorm (F : Mbar r' S) : ℝ≥0 := ∑ s, ∑' n, (↑(F s n).nat_abs * r' ^ n)

notation `∥`F`∥₊` := Mbar.nnnorm F

lemma nnnorm_def (F : Mbar r' S) : ∥F∥₊ = ∑ s, ∑' n, (↑(F s n).nat_abs * r' ^ n) := rfl

@[simp] lemma nnnorm_zero : ∥(0 : Mbar r' S)∥₊ = 0 :=
by simp only [nnnorm_def, Mbar.coe_zero, tsum_zero, nat.cast_zero, zero_mul, pi.zero_apply,
    zero_le', finset.sum_const_zero, int.nat_abs_zero]

@[simp] lemma nnnorm_neg (F : Mbar r' S) : ∥-F∥₊ = ∥F∥₊ :=
by simp only [nnnorm_def, Mbar.coe_neg, pi.neg_apply, int.nat_abs_neg, int.nat_abs,
  coe_neg, set.mem_set_of_eq]

lemma nnnorm_add_le (F₁ F₂ : Mbar r' S) : ∥F₁ + F₂∥₊ ≤ ∥F₁∥₊ + ∥F₂∥₊ :=
begin
  simp only [nnnorm_def, ← finset.sum_add_distrib],
  refine finset.sum_le_sum _,
  rintro s -,
  rw ← tsum_add (F₁.summable s) (F₂.summable s),
  refine tsum_le_tsum _ ((F₁ + F₂).summable _) ((F₁.summable s).add (F₂.summable s)),
  intro n,
  dsimp,
  rw [← add_mul, ← nat.cast_add],
  apply mul_le_mul_right',
  rw nat.cast_le,
  exact int.nat_abs_add_le _ _
end

lemma nnnorm_sum_le {ι : Type*} (s : finset ι) (F : ι → Mbar r' S) :
  ∥∑ i in s, F i∥₊ ≤ ∑ i in s, ∥F i∥₊ :=
begin
  classical,
  apply finset.induction_on s; clear s,
  { simp only [finset.sum_empty, nnnorm_zero] },
  intros i s his IH,
  simp only [finset.sum_insert his],
  exact (nnnorm_add_le _ _).trans (add_le_add le_rfl IH)
end

instance pseudo_normed_group : pseudo_normed_group (Mbar r' S) :=
{ filtration := λ c, {F | ∥F∥₊ ≤ c},
  filtration_mono := λ c₁ c₂ h F hF, le_trans (by exact hF) h, -- `by exact`, why??
  zero_mem_filtration := λ c, by { dsimp, rw nnnorm_zero, apply zero_le' },
  neg_mem_filtration := λ c F hF, by { dsimp, rwa nnnorm_neg },
  add_mem_filtration := λ c₁ c₂ F₁ F₂ hF₁ hF₂,
  by exact le_trans (nnnorm_add_le _ _) (add_le_add hF₁ hF₂) }

lemma mem_filtration_iff (x : Mbar r' S) (c : ℝ≥0) :
  x ∈ pseudo_normed_group.filtration (Mbar r' S) c ↔ ∥x∥₊ ≤ c :=
iff.rfl

/--
The coercion from `Mbar r' S` to functions `S → ℕ → ℤ`.
This is an additive group homomorphism.
-/
def coe_hom : Mbar r' S →+ (S → ℕ → ℤ) :=
add_monoid_hom.mk' coe_fn $ coe_add

@[simp] lemma coe_sum {ι : Type*} (s : finset ι) (F : ι → Mbar r' S) :
  ⇑(∑ i in s, F i) = ∑ i in s, (F i) :=
show coe_hom (∑ i in s, F i) = ∑ i in s, coe_hom (F i), from add_monoid_hom.map_sum _ _ _

@[simp] lemma coe_gsmul (n : ℤ) (F : Mbar r' S) : ⇑(n • F) = n • F :=
show coe_hom (n • F) = n • coe_hom F, from add_monoid_hom.map_gsmul _ _ _

@[simp] lemma coe_smul (n : ℤ) (F : Mbar r' S) : ⇑(n • F) = n • F :=
coe_gsmul _ _

@[simp] lemma coe_nsmul (n : ℕ) (F : Mbar r' S) : ⇑(n • F) = n • F :=
by simpa only [gsmul_coe_nat] using coe_gsmul ↑n F

@[simp] lemma nnnorm_smul (N : ℤ) (F : Mbar r' S) : ∥N • F∥₊ = nnnorm N * ∥F∥₊ :=
begin
  simp only [nnnorm_def, finset.mul_sum],
  apply fintype.sum_congr,
  intro s,
  apply nnreal.eq,
  simp only [nnreal.coe_mul, nnreal.coe_tsum, ← tsum_mul_left, ← mul_assoc,
    nnreal.coe_nat_abs, coe_nnnorm, coe_smul, pi.smul_apply, int.norm_def,
    ← abs_mul, ← int.cast_mul, smul_eq_mul],
end

section Tinv

/--
The action of T⁻¹.
-/
def Tinv_aux {R : Type*} [has_zero R] : (ℕ → R) → ℕ → R := λ F n, if n = 0 then 0 else F (n + 1)

@[simp] lemma Tinv_aux_zero {R : Type*} [has_zero R] (f : ℕ → R) : Tinv_aux f 0 = 0 := rfl

@[simp] lemma Tinv_aux_ne_zero {R : Type*} [has_zero R] (f : ℕ → R) (i : ℕ) (hi : i ≠ 0) :
  Tinv_aux f i = f (i + 1) :=
if_neg hi

@[simp] lemma Tinv_aux_succ {R : Type*} [has_zero R] (f : ℕ → R) (i : ℕ) :
  Tinv_aux f (i + 1) = f (i + 2) :=
if_neg (nat.succ_ne_zero i)

lemma Tinv_aux_summable [h0r : fact (0 < r')] (F : Mbar r' S) (s : S) :
  summable (λ n, (↑(Tinv_aux (F s) n).nat_abs * r' ^ n)) :=
begin
  have : ∀ n:ℕ, r' ^ n = r' ^ n * r' * r'⁻¹,
  { intro, rw [mul_inv_cancel_right' h0r.out.ne'] },
  conv { congr, funext, rw [this, ← mul_assoc] },
  apply summable.mul_right,
  refine nnreal.summable_of_le _ (nnreal.summable_nat_add _ (F.summable s) 1),
  rintro ⟨i⟩,
  { simp only [nat.cast_zero, zero_mul, Tinv_aux_zero, zero_le', int.nat_abs_zero] },
  { simp only [Tinv_aux_succ, pow_add, mul_assoc, pow_one] }
end

/--
The `T⁻¹` action on `Mbar r' S`.
This is defined, essentially, as a shift in `ℕ` (accounting for the restriction at 0).
This is an additive group homomorphism.
-/
def Tinv {r : ℝ≥0} {S : Type u} [fintype S] [h0r : fact (0 < r)] :
  Mbar r S →+ Mbar r S :=
add_monoid_hom.mk' (λ F,
  { to_fun := λ s, Tinv_aux (F s),
    coeff_zero' := λ s, rfl,
    summable' := Tinv_aux_summable F })
  begin
    intros F G,
    ext s (_|n),
    { simp only [add_zero, pi.add_apply, Mbar.coeff_zero] },
    { simp only [coe_mk, pi.add_apply, Tinv_aux_succ, coe_add] }
  end

@[simp] lemma Tinv_zero [fact (0 < r')] (F : Mbar r' S) (s : S) : Tinv F s 0 = 0 := rfl

@[simp] lemma Tinv_ne_zero [fact (0 < r')] (F : Mbar r' S) (s : S) (i : ℕ) (hi : i ≠ 0) :
  Tinv F s i = F s (i + 1) :=
if_neg hi

@[simp] lemma Tinv_succ [fact (0 < r')] (F : Mbar r' S) (s : S) (i : ℕ) :
  Tinv F s (i + 1) = F s (i + 2) :=
Tinv_aux_succ (F s) i

open pseudo_normed_group

lemma Tinv_mem_filtration [h0r : fact (0 < r')] :
  Tinv ∈ filtration (Mbar r' S →+ Mbar r' S) (r'⁻¹) :=
begin
  intros c F hF,
  simp only [Tinv, add_monoid_hom.mk'_apply],
  change _ ≤ _ at hF,
  rw mul_comm,
  apply le_mul_inv_of_mul_le h0r.out.ne',
  rw [nnnorm_def, finset.sum_mul],
  apply le_trans _ hF,
  apply finset.sum_le_sum,
  rintro s -,
  rw ← nnreal.tsum_mul_right,
  conv_rhs { rw [← sum_add_tsum_nat_add' 1 (F.summable s)] },
  refine le_add_of_nonneg_of_le zero_le' _,
  apply tsum_le_tsum,
  { rintro (_|i),
    { simp only [nat.cast_zero, zero_mul, Mbar.coeff_zero, int.nat_abs_zero], exact zero_le' },
    { simp only [Tinv_aux_succ, mul_assoc, coe_mk, pow_succ'] } },
  { exact (Tinv_aux_summable F s).mul_right _ },
  { exact (nnreal.summable_nat_add_iff 1).mpr (F.summable s) }
end

end Tinv

lemma archimedean : pseudo_normed_group.archimedean (Mbar r' S) :=
begin
  intros x c N hN,
  simp only [Mbar.mem_filtration_iff],
  have hN' : 0 < (N : ℝ≥0) := by exact_mod_cast hN,
  conv_rhs { rw ← mul_le_mul_left hN' },
  simp only [nnnorm_def, nsmul_eq_mul, finset.mul_sum, finset.sum_mul,
    coe_nsmul, pi.mul_apply, pi.nat_apply, @pi.nat_apply ℕ ℤ _ _ _ N,
    int.nat_abs_mul, int.nat_abs_of_nat, int.nat_cast_eq_coe_nat, nat.cast_mul],
  convert iff.rfl,
  ext s,
  simp only [nnreal.coe_nat_cast, nnreal.coe_tsum, nnreal.coe_mul, ← tsum_mul_left, ← mul_assoc]
end

/-- `of_mask x mask : Mbar r' S` is `∑ a_{s,n}T^n ∈ Tℤ[[T]]`,
where `a_{s,n}` is `x_{s,n}` if `mask n s` is true and `0` otherwise. -/
@[simps]
def of_mask (x : Mbar r' S) (mask : S → ℕ → Prop) [∀ s n, decidable (mask s n)] :
  Mbar r' S :=
{ to_fun := λ s n, if mask s n then x s n else 0,
  coeff_zero' := λ s, by { split_ifs, { exact x.coeff_zero s }, { refl } },
  summable' := λ s,
  begin
    apply nnreal.summable_of_le _ (x.summable s),
    intro n,
    refine mul_le_mul' _ le_rfl,
    norm_cast,
    split_ifs,
    { refl },
    { rw int.nat_abs_zero, exact zero_le' }
  end }

variables (r' S)

/-- `geom r' S` is `∑ T^n ∈ Tℤ[[T]]`.
In other words, all non-constant coefficients are `1`. -/
@[simps]
def geom [hr' : fact (r' < 1)] : Mbar r' S :=
{ to_fun := λ s n, if n = 0 then 0 else 1,
  coeff_zero' := λ s, if_pos rfl,
  summable' := λ s,
  begin
    have := (normed_ring.summable_geometric_of_norm_lt_1 (r' : ℝ) _), swap,
    { rw nnreal.norm_eq, exact hr'.out },
    simp only [← nnreal.coe_pow, nnreal.summable_coe] at this,
    apply nnreal.summable_of_le _ this,
    intro n,
    refine (mul_le_mul' _ le_rfl).trans (one_mul _).le,
    split_ifs; simp
  end }

end Mbar

#lint- only unused_arguments def_lemma doc_blame
