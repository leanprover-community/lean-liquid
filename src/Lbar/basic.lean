import data.real.basic
import algebra.big_operators.basic
import topology.algebra.infinite_sum
import data.finset.basic
import logic.equiv.basic
import analysis.normed_space.basic
import analysis.specific_limits.normed

import Lbar.bounded
import pseudo_normed_group.basic

import for_mathlib.tsum

/-!

## $\overline{\mathcal{M}}_{r'}(S)$

This file contains a definition of `ℳ-bar_{r'}(S) as defined at the very beginning
of section 9 of `Analytic.pdf` (p57), and its action of `T⁻¹`.

## Implementation issues

We model Tℤ[[T]] as functions ℕ → ℤ which vanish at 0.

-/

universe u

noncomputable theory
open_locale big_operators nnreal

section defs

set_option old_structure_cmd true

/-- `Lbar r S` is the set of power series
`F_s = ∑ a_{s,n}T^n ∈ Tℤ[[T]]` such that `∑_{s,n} |a_{s,n}|r^n` converges
(or equivalently, because `S` is a finite type, such that for each `s : S`,
`∑_n |a_{s,n}|r^n` converges. ) -/
structure Lbar (r' : ℝ≥0) (S : Type u) [fintype S] :=
(to_fun      : S → ℕ → ℤ)
(coeff_zero' : ∀ s, to_fun s 0 = 0)
(summable'   : ∀ s, summable (λ n, (↑(to_fun s n).nat_abs * r' ^ n)))

end defs

variables {r' : ℝ≥0} {S : Type u} [fintype S]

namespace Lbar

instance has_coe_to_fun : has_coe_to_fun (Lbar r' S) (λ _, S → ℕ → ℤ) := ⟨Lbar.to_fun⟩

@[simp] lemma coe_mk (x h₁ h₂) : ((⟨x, h₁, h₂⟩ : Lbar r' S) : S → ℕ → ℤ) = x := rfl

@[simp] protected lemma coeff_zero (x : Lbar r' S) (s : S) : x s 0 = 0 := x.coeff_zero' s

protected lemma summable (x : Lbar r' S) (s : S) :
  summable (λ n, (↑(x s n).nat_abs * r' ^ n)) := x.summable' s

lemma summable_coe_real (x : Lbar r' S) (s : S) :
  summable (λ n, ∥x s n∥ * r' ^ n) :=
by simpa only [← nnreal.summable_coe, nnreal.coe_nat_cast, nnreal.coe_nat_abs,
  nnreal.coe_mul, nnreal.coe_pow] using x.summable s

@[ext] lemma ext (x y : Lbar r' S) (h : (⇑x : S → ℕ → ℤ) = y) : x = y :=
by { cases x, cases y, congr, exact h }

lemma ext_iff (x y : Lbar r' S) : x = y ↔ (x : S → ℕ → ℤ) = y :=
⟨congr_arg _, ext x y⟩

/-- The zero element of `Lbar r' S`, defined as the constant 0-function. -/
def zero : Lbar r' S :=
{ to_fun := 0,
  coeff_zero' := λ s, rfl,
  summable' := λ s, by simpa using summable_zero }

/-- Addition in `Lbar r' S`, defined as pointwise addition. -/
def add (F : Lbar r' S) (G : Lbar r' S) : Lbar r' S :=
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

/-- Subtraction in `Lbar r' S`, defined as pointwise subtraction. -/
def sub (F : Lbar r' S) (G : Lbar r' S) : Lbar r' S :=
{ to_fun := F - G,
  coeff_zero' := λ s, by simp [F.coeff_zero s, G.coeff_zero s],
  summable' :=
  begin
    intro s,
    apply nnreal.summable_of_le _ ((F.summable s).add (G.summable s)),
    intro n,
    rw [← add_mul, ← nat.cast_add],
    apply mul_le_mul_right',
    rw nat.cast_le,
    exact int.nat_abs_sub_le _ _
  end }

/-- Negation in `Lbar r' S`, defined as pointwise negation. -/
def neg (F : Lbar r' S) : Lbar r' S :=
{ to_fun := -F,
  coeff_zero' := λ s, by simp [F.coeff_zero s],
  summable' :=
  begin
    intro s,
    convert F.summable s using 1,
    ext n,
    simp only [pi.neg_apply, int.nat_abs_neg]
  end }

instance : has_zero (Lbar r' S) := ⟨zero⟩
instance : has_add (Lbar r' S) := ⟨add⟩
instance : has_sub (Lbar r' S) := ⟨sub⟩
instance : has_neg (Lbar r' S) := ⟨neg⟩

instance : inhabited (Lbar r' S) := ⟨0⟩

@[simp] lemma coe_zero : ⇑(0 : Lbar r' S) = 0 := rfl
@[simp] lemma coe_add (F G : Lbar r' S) : ⇑(F + G : Lbar r' S) = F + G := rfl
@[simp] lemma coe_sub (F G : Lbar r' S) : ⇑(F - G : Lbar r' S) = F - G := rfl
@[simp] lemma coe_neg (F : Lbar r' S) : ⇑(-F : Lbar r' S) = -F := rfl

--instance fff : topological_ring ℝ≥0 :=
--{ continuous_add := continuous_add,
--  continuous_mul := continuous_mul }

/-- Tailored scalar multiplication by natural numbers. -/
protected def nsmul (N : ℕ) (F : Lbar r' S) : Lbar r' S :=
{ to_fun := λ s n, N • F s n,
  coeff_zero' := λ s, by simp only [F.coeff_zero, smul_zero],
  summable' := λ s,
  begin
    convert summable.mul_left ↑N (F.summable' s),
    ext,
    simp only [←mul_assoc, nsmul_eq_mul, int.nat_cast_eq_coe_nat, nonneg.coe_mul, int.nat_abs_mul],
    norm_cast
  end }

/-- Tailored scalar multiplication by integers. -/
protected def zsmul (N : ℤ) (F : Lbar r' S) : Lbar r' S :=
{ to_fun := λ s n, N • F s n,
  coeff_zero' := λ s, by simp only [F.coeff_zero, smul_zero],
  summable' := λ s,
  begin
    refine nnreal.summable_coe.mp _,
    convert summable.mul_left ↑N.nat_abs (nnreal.summable_coe.mpr (F.summable' s)),
    ext,
    simp only [←mul_assoc, int.nat_abs_mul, smul_eq_mul, nat.cast_mul, nonneg.coe_mul],
    norm_cast,
  end }

instance : add_comm_group (Lbar r' S) :=
{ zero := 0, add := (+), sub := has_sub.sub, neg := has_neg.neg,
  zero_add := by { intros, ext, simp only [coe_zero, zero_add, coe_add] },
  add_zero := by { intros, ext, simp only [coe_zero, add_zero, coe_add] },
  add_assoc := by { intros, ext, simp only [add_assoc, coe_add] },
  add_left_neg := by { intros, ext,
    simp only [coe_add, coe_neg, coe_zero, pi.add_apply, pi.zero_apply, pi.neg_apply, add_left_neg] },
  add_comm := by { intros, ext, simp only [coe_add, add_comm] },
  sub_eq_add_neg := by { intros, ext, simp only [coe_sub, coe_add, coe_neg, sub_eq_add_neg] },
  nsmul := λ n F, F.nsmul n,
  nsmul_zero' := λ F, by { ext, simp only [Lbar.nsmul, zero_smul], refl },
  nsmul_succ' := λ n F,
  begin
    ext,
    simp only [Lbar.nsmul, nat.succ_eq_add_one, add_smul, one_smul, add_comm, coe_mk, coe_add,
      pi.add_apply],
  end,
  zsmul := λ n F, F.zsmul n,
  zsmul_zero' := λ F, by { ext, simp only [Lbar.zsmul, zero_smul], refl },
  zsmul_succ' := λ n F,
  begin
    ext,
    simp only [Lbar.zsmul, nat.succ_eq_add_one, algebra.id.smul_eq_mul, coe_mk, pi.add_apply,
      int.coe_nat_succ, int.of_nat_eq_coe, coe_add, add_mul, one_mul, add_comm],
  end,
  zsmul_neg' := λ n F,
  begin
    ext,
    simp only [Lbar.zsmul, algebra.id.smul_eq_mul, coe_mk, pi.neg_apply, int.coe_nat_succ, coe_neg,
      add_mul, one_mul, neg_add_rev, int.neg_succ_of_nat_coe, neg_mul, one_mul],
  end }

/-- The `coeff s n` is the additive homomorphism that sends `x : Lbar r' S`
to the coefficient `x_{s,n}`. -/
@[simps]
def coeff (s : S) (n : ℕ) : Lbar r' S →+ ℤ :=
{ to_fun := λ x, x s n,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

/-- The norm of `F : Lbar r' S` as nonnegative real number.
It is defined as `∑ s, ∑' n, (↑(F s n).nat_abs * r' ^ n)`. -/
protected def nnnorm (F : Lbar r' S) : ℝ≥0 := ∑ s, ∑' n, (↑(F s n).nat_abs * r' ^ n)

instance : has_nnnorm (Lbar r' S) := ⟨Lbar.nnnorm⟩

lemma nnnorm_def (F : Lbar r' S) : ∥F∥₊ = ∑ s, ∑' n, (↑(F s n).nat_abs * r' ^ n) := rfl

@[simp] lemma nnnorm_zero : ∥(0 : Lbar r' S)∥₊ = 0 :=
by simp only [nnnorm_def, Lbar.coe_zero, tsum_zero, nat.cast_zero, zero_mul, pi.zero_apply,
    zero_le', finset.sum_const_zero, int.nat_abs_zero]

@[simp] lemma nnnorm_neg (F : Lbar r' S) : ∥-F∥₊ = ∥F∥₊ :=
by simp only [nnnorm_def, Lbar.coe_neg, pi.neg_apply, int.nat_abs_neg, int.nat_abs,
  coe_neg, set.mem_set_of_eq]

lemma nnnorm_add_le (F₁ F₂ : Lbar r' S) : ∥F₁ + F₂∥₊ ≤ ∥F₁∥₊ + ∥F₂∥₊ :=
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

lemma nnnorm_sum_le {ι : Type*} (s : finset ι) (F : ι → Lbar r' S) :
  ∥∑ i in s, F i∥₊ ≤ ∑ i in s, ∥F i∥₊ :=
begin
  classical,
  apply finset.induction_on s; clear s,
  { simp only [finset.sum_empty, nnnorm_zero] },
  intros i s his IH,
  simp only [finset.sum_insert his],
  exact (nnnorm_add_le _ _).trans (add_le_add le_rfl IH)
end

instance pseudo_normed_group : pseudo_normed_group (Lbar r' S) :=
{ filtration := λ c, {F | ∥F∥₊ ≤ c},
  filtration_mono := λ c₁ c₂ h F hF, le_trans hF h,
  zero_mem_filtration := λ c, by { dsimp, rw nnnorm_zero, apply zero_le' },
  neg_mem_filtration := λ c F hF, by { dsimp, rwa nnnorm_neg },
  add_mem_filtration := λ c₁ c₂ F₁ F₂ hF₁ hF₂,
  by exact le_trans (nnnorm_add_le _ _) (add_le_add hF₁ hF₂) }

lemma mem_filtration_iff (x : Lbar r' S) (c : ℝ≥0) :
  x ∈ pseudo_normed_group.filtration (Lbar r' S) c ↔ ∥x∥₊ ≤ c :=
iff.rfl

/--
The coercion from `Lbar r' S` to functions `S → ℕ → ℤ`.
This is an additive group homomorphism.
-/
def coe_hom : Lbar r' S →+ (S → ℕ → ℤ) :=
add_monoid_hom.mk' coe_fn $ coe_add

@[simp] lemma coe_sum {ι : Type*} (s : finset ι) (F : ι → Lbar r' S) :
  ⇑(∑ i in s, F i) = ∑ i in s, (F i) :=
show coe_hom (∑ i in s, F i) = ∑ i in s, coe_hom (F i), from add_monoid_hom.map_sum _ _ _

@[simp] lemma coe_zsmul (n : ℤ) (F : Lbar r' S) : ⇑(n • F) = n • F := rfl

@[simp] lemma coe_nsmul (n : ℕ) (F : Lbar r' S) : ⇑(n • F) = n • F := rfl

@[simp] lemma nnnorm_zsmul (N : ℤ) (F : Lbar r' S) : ∥N • F∥₊ = ∥N∥₊ * ∥F∥₊ :=
begin
  simp only [nnnorm_def, finset.mul_sum],
  apply fintype.sum_congr,
  intro s,
  apply nnreal.eq,
  simp only [nnreal.coe_mul, nnreal.coe_tsum, ← tsum_mul_left, ← mul_assoc,
    nnreal.coe_nat_abs, coe_nnnorm, coe_zsmul, pi.smul_apply, int.norm_eq_abs,
    ← abs_mul, ← int.cast_mul, smul_eq_mul],
end

lemma nnnorm_nsmul (x : Lbar r' S) (N : ℕ) : ∥N • x∥₊ = N • ∥x∥₊ :=
by { rw [← coe_nat_zsmul, nnnorm_zsmul, nsmul_eq_mul, ← nnreal.coe_nat_abs], refl, }

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

lemma Tinv_aux_summable [h0r : fact (0 < r')] (F : Lbar r' S) (s : S) :
  summable (λ n, (↑(Tinv_aux (F s) n).nat_abs * r' ^ n)) :=
begin
  have : ∀ n : ℕ, r' ^ n = r' ^ n * r' * r'⁻¹,
  { intro, rw [mul_inv_cancel_right₀ h0r.out.ne'] },
  conv { congr, funext, rw [this, ← mul_assoc] },
  apply summable.mul_right,
  refine nnreal.summable_of_le _ (nnreal.summable_nat_add _ (F.summable s) 1),
  rintro ⟨i⟩,
  { simp only [nat.cast_zero, zero_mul, Tinv_aux_zero, zero_le', int.nat_abs_zero] },
  { simp only [Tinv_aux_succ, pow_add, mul_assoc, pow_one] }
end

/--
The `T⁻¹` action on `Lbar r' S`.
This is defined, essentially, as a shift in `ℕ` (accounting for the restriction at 0).
This is an additive group homomorphism.
-/
def Tinv {r : ℝ≥0} {S : Type u} [fintype S] [h0r : fact (0 < r)] :
  Lbar r S →+ Lbar r S :=
add_monoid_hom.mk' (λ F,
  { to_fun := λ s, Tinv_aux (F s),
    coeff_zero' := λ s, rfl,
    summable' := Tinv_aux_summable F })
  begin
    intros F G,
    ext s (_|n),
    { simp only [add_zero, pi.add_apply, Lbar.coeff_zero] },
    { simp only [coe_mk, pi.add_apply, Tinv_aux_succ, coe_add] }
  end

@[simp] lemma Tinv_zero [fact (0 < r')] (F : Lbar r' S) (s : S) : Tinv F s 0 = 0 := rfl

@[simp] lemma Tinv_ne_zero [fact (0 < r')] (F : Lbar r' S) (s : S) (i : ℕ) (hi : i ≠ 0) :
  Tinv F s i = F s (i + 1) :=
if_neg hi

@[simp] lemma Tinv_succ [fact (0 < r')] (F : Lbar r' S) (s : S) (i : ℕ) :
  Tinv F s (i + 1) = F s (i + 2) :=
Tinv_aux_succ (F s) i

open pseudo_normed_group

lemma Tinv_mem_filtration [h0r : fact (0 < r')] :
  Tinv ∈ filtration (Lbar r' S →+ Lbar r' S) (r'⁻¹) :=
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
    { simp only [nat.cast_zero, zero_mul, Lbar.coeff_zero, int.nat_abs_zero], exact zero_le' },
    { simp only [Tinv_aux_succ, mul_assoc, coe_mk, pow_succ'] } },
  { exact (Tinv_aux_summable F s).mul_right _ },
  { exact (nnreal.summable_nat_add_iff 1).mpr (F.summable s) }
end

end Tinv

/-- `of_mask x mask : Lbar r' S` is `∑ a_{s,n}T^n ∈ Tℤ[[T]]`,
where `a_{s,n}` is `x_{s,n}` if `mask n s` is true and `0` otherwise. -/
@[simps]
def of_mask (x : Lbar r' S) (mask : S → ℕ → Prop) [∀ s n, decidable (mask s n)] :
  Lbar r' S :=
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
def geom [hr' : fact (r' < 1)] : Lbar r' S :=
{ to_fun := λ s n, if n = 0 then 0 else 1,
  coeff_zero' := λ s, if_pos rfl,
  summable' := λ s,
  begin
    have := (@summable_geometric_of_norm_lt_1 _ _ (r' : ℝ) _), swap,
    { rw nnreal.norm_eq, exact hr'.out },
    simp only [← nnreal.coe_pow, nnreal.summable_coe] at this,
    apply nnreal.summable_of_le _ this,
    intro n,
    refine (mul_le_mul' _ le_rfl).trans (one_mul _).le,
    split_ifs; simp
  end }

section map

variables {r' S} {T : Type*} [fintype T] (f : S → T)

open_locale classical

lemma has_sum_aux (F : Lbar r' S) :
  has_sum (λ n : ℕ, (∑ s, ↑(F s n).nat_abs) * r' ^ n) (∑ s, ∑' n, (F s n).nat_abs * r' ^ n) :=
begin
  have : (λ (n : ℕ), (∑ (s : S), ↑(F s n).nat_abs) * r' ^ n) =
    (λ (n : ℕ), ∑ (s : S), (↑(F s n).nat_abs) * r' ^ n),
  { funext n,
    rw finset.sum_mul },
  rw this, clear this,
  exact has_sum_sum (λ s _, (F.summable s).has_sum)
end

/-- Given an element of `Lbar r' S` and a function `f : S → T`, this
  constructs an associated element of `Lbar r' T`. -/
@[simps]
def map : Lbar r' S → Lbar r' T := λ F,
{ to_fun := λ t n, ∑ s in finset.univ.filter (λ s', f s' = t), F s n,
  coeff_zero' := λ s, by simp,
  summable' := λ t, begin
    have : ∀ (n : ℕ),
      ↑((∑ (s : S) in finset.univ.filter (λ (s' : S), f s' = t), F s n).nat_abs) * r' ^ n ≤
      (∑ s : S, (F s n).nat_abs) * r' ^ n,
    { intro n,
      refine mul_le_mul _ (le_refl _) zero_le' zero_le',
      simp_rw ← nat.cast_sum,
      apply nat.cast_le.mpr,
      have : (∑ (s : S) in finset.univ.filter (λ (s' : S), f s' = t), F s n).nat_abs ≤
        ∑ (s : S) in finset.univ.filter (λ s', f s' = t), (F s n).nat_abs,
      { apply nat_abs_sum_le },
      refine le_trans this _,
      apply finset.sum_le_sum_of_subset,
      { intros t ht, simp },
      { apply_instance } },
    exact nnreal.summable_of_le this (has_sum.summable (has_sum_aux _)),
  end }

lemma map_id (F : Lbar r' S) : F.map id = F :=
begin
  ext s n,
  simp [finset.sum_filter],
end

lemma map_comp (F : Lbar r' S) {U : Type*} [fintype U] (g : T → U) :
  F.map (g ∘ f) = (F.map f).map g :=
begin
  ext u n,
  dsimp,
  rw ← finset.sum_bUnion,
  { apply finset.sum_congr,
    ext s,
    split,
    { intro hs,
      simpa using hs },
    { intro hs,
      simpa using hs },
    { tauto } },
  { rintros t1 ht1 t2 ht2 h s hs,
    simp at ht1 ht2 hs ⊢,
    refine h _,
    rw [← hs.1, ← hs.2] }
end

lemma nnnorm_map_le_of_nnnorm_le {c : ℝ≥0} (F : Lbar r' S) (hF : ∥ F ∥₊ ≤ c) :
  ∥ F.map f ∥₊ ≤ c :=
begin
  simp [ Lbar.nnnorm_def ] at *,
  rw ← tsum_sum at hF ⊢,
  { refine le_trans (tsum_le_tsum _ _ _) hF,
    { intros n,
      simp_rw ← finset.sum_mul,
      refine mul_le_mul _ (le_refl _) zero_le' zero_le',
      simp_rw ← nat.cast_sum,
      rw nat.cast_le,
      have : ∑ (x : T), (∑ (s : S) in finset.univ.filter (λ (s' : S), f s' = x), F s n).nat_abs ≤
        ∑ (x : T), (∑ (s : S) in finset.univ.filter (λ s', f s' = x), (F s n).nat_abs),
      { apply finset.sum_le_sum,
        intros t ht,
        apply nat_abs_sum_le },
      refine le_trans this _,
      rw ← finset.sum_bUnion,
      apply finset.sum_le_sum_of_subset,
      { intros t ht, simp },
      { intros t1 ht1 t2 ht2 h s hs,
        simp at ht1 ht2 hs ⊢,
        apply h,
        rw [← hs.1, ← hs.2] } },
    { apply summable_sum,
      intros t ht,
      apply (F.map f).summable },
    { apply summable_sum,
      intros s hs,
      apply F.summable } },
  { intros t ht,
    apply (F.map f).summable },
  { intros s hs,
    apply F.summable }
end

end map

end Lbar

#lint-
