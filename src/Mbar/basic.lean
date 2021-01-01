import data.real.basic
import algebra.big_operators.basic
import topology.algebra.infinite_sum
import data.finset.basic
import data.equiv.basic
import analysis.normed_space.basic
import analysis.specific_limits
import data.equiv.basic

import Mbar.bounded

import for_mathlib.tsum

/-!

## $\overline{\mathcal{M}}_{r'}(S)$

This file contains a definition of ℳ-barᵣ'(S) as defined on p57 of Analytic.pdf .

## Implementation issues

We model Tℤ[[T]] as functions ℕ → ℤ which vanish at 0.

-/

universe u

noncomputable theory
open_locale big_operators

section defs

set_option old_structure_cmd true

/-- `Mbar r' S` is the set of power series
`F_s = ∑ a_{n,s}T^n ∈ Tℤ[[T]]` such that `∑_{n,s} |a_{n,s}|r'^n` converges -/
structure Mbar (r' : ℝ) (S : Type u) [fintype S] :=
(to_fun : S → ℕ → ℤ)
(coeff_zero' : ∀ s, to_fun s 0 = 0)
(summable' : ∀ s, summable (λ n, abs ((to_fun s n : ℝ) * r' ^ n)))

/-- `Mbar_le r' S c` is the set of power series
`F_s = ∑ a_{n,s}T^n ∈ Tℤ[[T]]` such that `∑_{n,s} |a_{n,s}|r'^n ≤ c` -/
structure Mbar_le (r' : ℝ) (S : Type u) [fintype S] (c : ℝ) extends Mbar r' S :=
(sum_tsum_le' : (∑ s, ∑' n, (abs ((to_fun s n : ℝ) * r'^n))) ≤ c)

end defs

variables {r' : ℝ} {S : Type u} [fintype S]

namespace Mbar

instance has_coe_to_fun : has_coe_to_fun (Mbar r' S) := ⟨_, Mbar.to_fun⟩

@[simp] lemma coe_mk (x h₁ h₂) : ((⟨x, h₁, h₂⟩ : Mbar r' S) : S → ℕ → ℤ) = x := rfl

@[simp] protected lemma coeff_zero (x : Mbar r' S) (s : S) : x s 0 = 0 := x.coeff_zero' s

protected lemma summable (x : Mbar r' S) (s : S) :
  summable (λ n, abs ((x s n : ℝ) * r'^n)) := x.summable' s

lemma summable_nnabs (F : Mbar r' S) (s : S) :
  summable (λ (i : ℕ), real.nnabs ((F s i) * r' ^ i)) :=
by { rw ← nnreal.summable_coe, simpa only [nnreal.coe_nnabs] using F.summable s }

@[ext] lemma ext (x y : Mbar r' S) (h : ⇑x = y) : x = y :=
by { cases x, cases y, congr, exact h }

lemma ext_iff (x y : Mbar r' S) : x = y ↔ (x : S → ℕ → ℤ) = y :=
⟨congr_arg _, ext x y⟩

def zero : Mbar r' S :=
{ to_fun := 0,
  coeff_zero' := λ s, rfl,
  summable' := λ s, by simpa using summable_zero }

def add (F : Mbar r' S) (G : Mbar r' S) : Mbar r' S :=
{ to_fun := F + G,
  coeff_zero' := λ s, by simp [F.coeff_zero s, G.coeff_zero s],
  summable' :=
  begin
    intro s,
    have hFs := F.summable, have hGs := G.summable,
    simp_rw summable_abs_iff at hFs hGs ⊢,
    convert summable.add (hFs s) (hGs s),
    ext n,
    simp only [add_mul, int.cast_add, pi.add_apply]
  end }

def sub (F : Mbar r' S) (G : Mbar r' S) : Mbar r' S :=
{ to_fun := F - G,
  coeff_zero' := λ s, by simp [F.coeff_zero s, G.coeff_zero s],
  summable' :=
  begin
    intro s,
    have hFs := F.summable, have hGs := G.summable,
    simp_rw summable_abs_iff at hFs hGs ⊢,
    convert summable.sub (hFs s) (hGs s),
    ext n,
    simp only [sub_mul, int.cast_sub, pi.sub_apply]
  end }

def neg (F : Mbar r' S) : Mbar r' S :=
{ to_fun := -F,
  coeff_zero' := λ s, by simp [F.coeff_zero s],
  summable' :=
  begin
    intro s,
    convert F.summable s using 1,
    ext n,
    simp only [neg_mul_eq_neg_mul_symm, pi.neg_apply, abs_neg, int.cast_neg],
  end }

instance : has_zero (Mbar r' S) := ⟨zero⟩
instance : has_add (Mbar r' S) := ⟨add⟩
instance : has_sub (Mbar r' S) := ⟨sub⟩
instance : has_neg (Mbar r' S) := ⟨neg⟩

@[simp] lemma coe_zero : ⇑(0 : Mbar r' S) = 0 := rfl
@[simp] lemma coe_add (F G : Mbar r' S) : ⇑(F + G : Mbar r' S) = F + G := rfl
@[simp] lemma coe_sub (F G : Mbar r' S) : ⇑(F - G : Mbar r' S) = F - G := rfl
@[simp] lemma coe_neg (F : Mbar r' S) : ⇑(-F : Mbar r' S) = -F := rfl

instance : add_comm_group (Mbar r' S) :=
{ zero := 0, add := (+), sub := has_sub.sub, neg := has_neg.neg,
  zero_add := by { intros, ext, simp only [coe_zero, zero_add, coe_add] },
  add_zero := by { intros, ext, simp only [coe_zero, add_zero, coe_add] },
  add_assoc := by { intros, ext, simp only [add_assoc, coe_add] },
  add_left_neg := by { intros, ext, simp only [coe_add, coe_neg, coe_zero, add_left_neg] },
  add_comm := by { intros, ext, simp only [coe_add, add_comm] },
  sub_eq_add_neg := by { intros, ext, simp only [coe_sub, coe_add, coe_neg, sub_eq_add_neg] } }
.

instance : has_norm (Mbar r' S) :=
{ norm := λ F, ∑ s, ∑' n, (abs ((F s n : ℝ) * r'^n)) }

lemma norm_def (F : Mbar r' S) : ∥F∥ = ∑ s, ∑' n, (abs ((F s n : ℝ) * r'^n)) := rfl

instance [hr' : fact (0 < r')] : normed_group (Mbar r' S) :=
normed_group.of_core _
{ norm_eq_zero_iff :=
  begin
    intro F,
    rw [norm_def, finset.sum_eq_zero_iff_of_nonneg, ext_iff, function.funext_iff],
    { apply forall_congr,
      intro s,
      simp only [forall_prop_of_true, finset.mem_univ, coe_zero, pi.zero_apply,
        tsum_abs_eq_coe_tsum_nnabs],
      rw [← nnreal.coe_tsum, ← nnreal.coe_zero, nnreal.eq_iff,
          tsum_eq_zero_iff (F.summable_nnabs s), function.funext_iff],
      apply forall_congr,
      intro n,
      simp only [←nnreal.eq_iff, int.cast_eq_zero, abs_eq_zero, nnreal.coe_zero, pi.zero_apply,
        or_iff_left_iff_imp, nnreal.coe_nnabs, mul_eq_zero],
      intro H,
      exact (ne_of_gt hr' (pow_eq_zero H)).elim },
    { exact (λ _ _, tsum_nonneg (λ _, abs_nonneg _)) }
  end,
  triangle :=
  begin
    intros F G,
    simp only [norm_def],
    rw ← finset.sum_add_distrib,
    refine finset.sum_le_sum _,
    rintro s -,
    rw ← tsum_add (F.summable s) (G.summable s),
    refine tsum_le_tsum _ ((F + G).summable _) (summable.add (F.summable s) (G.summable s)),
    intro n,
    convert abs_add _ _,
    simp [add_mul]
  end,
  norm_neg :=
  begin
    intro F, rw [norm_def, norm_def],
    simp only [neg_mul_eq_neg_mul_symm, pi.neg_apply, abs_neg, int.cast_neg, coe_neg]
  end }

section Tinv

/-!
### The action of T⁻¹
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
  summable (λ (n : ℕ), abs (↑(Tinv_aux (F s) n) * r' ^ n)) :=
begin
  rw summable_mul_right_iff (ne_of_gt h0r),
  have H := F.summable s,
  refine summable_of_norm_bounded _ ((summable_nat_add_iff 1).mpr H) _,
  rintro ⟨i⟩,
  { simp only [abs_nonneg, norm_zero, int.cast_zero, zero_mul, abs_zero, Tinv_aux_zero]},
  { simp only [Tinv_aux_succ, real.norm_eq_abs, abs_mul, pow_add, mul_assoc, pow_one, abs_abs] },
end

@[simps]
def Tinv {r : ℝ} {S : Type u} [fintype S] [h0r : fact (0 < r)] (F : Mbar r S) :
  Mbar r S :=
{ to_fun := λ s, Tinv_aux (F s),
  coeff_zero' := λ s, rfl,
  summable' := Tinv_aux_summable F }

end Tinv

end Mbar
