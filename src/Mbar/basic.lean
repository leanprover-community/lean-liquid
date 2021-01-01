import data.real.basic
import algebra.big_operators.basic
import topology.algebra.infinite_sum
import data.finset.basic
import data.equiv.basic
import analysis.normed_space.basic
import analysis.specific_limits
import data.equiv.basic

import Mbar.bounded
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

@[ext] lemma ext (x y : Mbar r' S) (h : ⇑x = y) : x = y :=
by { cases x, cases y, congr, exact h }

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

-- instance : add_comm_group (Mbar r' S) :=
-- { zero := zero,
--   add := add,
--   sub := sub,
--   neg := neg, }

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
