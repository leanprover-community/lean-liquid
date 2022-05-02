import data.real.nnreal
import topology.algebra.infinite_sum
import analysis.normed_space.basic
import for_mathlib.nnreal

open_locale nnreal

/-

## An auxiliary lemma.

In this file we prove the following technical lemma.

Say `f : ℤ → ℝ` and `r : ℝ≥0` with `2⁻¹<r<1`.
Say the support of `f` is bounded below by `d` (i.e. `n < d → f n = 0`),
that `∑' (n : ℤ), ∥f n∥₊ * r ^ n` converges and is `≤ c`,
and furthermore that `∑' (n : ℤ), f n * 2⁻¹ ^ n = 0` (note that this
sum converges as 2⁻¹ < r).

Then `∑' (n : ℤ), ∥ite (d ≤ n)`
  `((finset.range (n - d).nat_abs.succ).sum (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l))`
  `0∥₊ * r ^ n` also converges and is `≤ c * r/(2r-1)` where `C` is some fixed constant
  depending only on `r` and not on `f`.

If we think of as `f` as the power series `∑ₙ f(n)Tⁿ ∈ ℤ[[T]][T⁻¹]`  then the
second sum is the norm of `f / (T⁻¹ - 2)`.

## The maths proof

  ∑(n ≥ d) ∥∑(0≤i≤(n-d)) f(n - 1 - i)*2ⁱ∥ * r^n
= ∑(n ≥ d) ∥∑(i≥0) f(n - 1 - i)2ⁱ∥ * rⁿ (as f(n-1-i) vanishes for i larger than n-d)
= ∑(n ≥ d) ∥(i<0) f(n - 1 - i)2ⁱ∥ * rⁿ (as sum f(x)2⁻ˣ=0)
= ∑(n ≥ d) ∥∑(k≥0) f(n + k) 2^(-1-k)∥ * rⁿ (set k=-1-i)
≤ ∑(n ≥ d) ∑(k≥0)∥ f(n+k)∥ 2^(-1-k) r^n (Cauchy-Schwarz)
= ∑(k≥0) ∑(n≥d) ∥f(n+k)∥2^(-1-k)r^n (turns out you can interchange the sums)
= 2⁻¹∑(k≥0) (∑(n≥d) ∥f(n+k)∥r^(n+k)) (2r)^{-k} (rearranging)
≤ 2⁻¹∑(k≥0) c (2r)^{-k} = 2⁻¹c/(1-(2r)⁻¹)= c*r/(2r-1).

We need to keep track of both the sums and the fact that things are summable.


## The Lean statement

lemma key_tsum_lemma (f : ℤ → ℝ) (r : ℝ≥0) (hr1 : r < 1) (hr2 : 2⁻¹ < r) (d : ℤ)
  (hdf : ∀ n, n < d → f n = 0) (hconv : summable (λ n : ℤ, ∥f n∥₊ * r ^ n))
  (hzero : ∑' n, f n *  2⁻¹ ^ n = 0) :
∑' (n : ℤ), ∥ite (d ≤ n) ((finset.range (n - d).nat_abs.succ).sum
  (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l)) 0∥₊ * r ^ n ≤
  r/(2*r-1) * ∑' n, ∥f n∥₊ * r ^ n := sorry

TODO:

Switch to ennreal and then prove 6 lemmas?
-/

lemma real.nnnorm_int (n : ℤ) : ∥(n : ℝ)∥₊ = ∥n∥₊ :=
subtype.ext $ by simp [coe_nnnorm, real.norm_eq_abs, int.norm_eq_abs]

namespace psi_aux_lemmas

lemma key_tsum_lemma (f : ℤ → ℝ) (r : ℝ≥0) (hr1 : r < 1) (hr2 : 2⁻¹ < r) (d : ℤ)
  (hdf : ∀ n, n < d → f n = 0) (hconv : summable (λ n : ℤ, ∥f n∥₊ * r ^ n))
  (hzero : ∑' n, f n *  2⁻¹ ^ n = 0) :
∑' (n : ℤ), ∥ite (d ≤ n) ((finset.range (n - d).nat_abs.succ).sum
  (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l)) 0∥₊ * r ^ n ≤
  (2 - r⁻¹)⁻¹ * ∑' n, ∥f n∥₊ * r ^ n :=
begin
  sorry
end

end psi_aux_lemmas

-- do I want z : ℝ≥0 here?
-- construction of C₄ function for z>0
noncomputable def C4_aux_function {z : ℝ} (d : ℤ) (hd : 2⁻¹ ^ d ≤ z) (h' : z < 2⁻¹ ^ (d + 1)) :
ℕ → ℕ × ℝ
| 0 := ⟨⌊z / (2⁻¹ ^ d)⌋₊, z - ⌊z / (2⁻¹ ^ d)⌋₊ * 2⁻¹ ^ d⟩
| (n + 1) := ⟨⌊(C4_aux_function n).2 / 2⁻¹⌋₊,
  (C4_aux_function n).2 - ⌊(C4_aux_function n).2 * 2⌋₊ * 2⁻¹⟩

lemma useful {z : ℝ} (hz : 0 < z) : ∃ d : ℤ, 2⁻¹ ^ d ≤ z ∧ z < 2⁻¹ ^ (d + 1) :=
begin
  sorry
end

noncomputable def C4_actual_function (z : ℝ) : ℤ → ℤ :=
if hz : 0 < z then (λ m, if m < (useful hz).some then 0 else (C4_aux_function (useful hz).some
  (useful hz).some_spec.1 (useful hz).some_spec.2 (m - (useful hz).some).nat_abs).1)
else if hz : 0 < -z then (λ m, if m < (useful hz).some then 0 else -(C4_aux_function (useful hz).some
  (useful hz).some_spec.1 (useful hz).some_spec.2 (m - (useful hz).some).nat_abs).1)
else 0

-- todo: (1) sums to z at 1/2, (2) r'-sum bounded by some random function (here r'=(2⁻¹)ᵖ)
