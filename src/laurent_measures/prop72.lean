import data.real.nnreal
import topology.algebra.infinite_sum
import analysis.normed_space.basic
import for_mathlib.nnreal

open_locale nnreal

/-

# Two auxiliary lemmas.

In this file we prove two technical lemmas, needed in the proofs of parts (2) and (4)
of Proposition 7.2 of `Analytic.pdf`.

## Lemma 1 (needed in part 2)

Say `f : ℤ → ℝ` and `r : ℝ≥0` with `2⁻¹<r<1`.
Say the support of `f` is bounded below by `d` (i.e. `n < d → f n = 0`),
We think of `f` as a power series `∑ₙf(n)Tⁿ` in `ℤ⟦T⟧[T⁻¹]`.

Here's the set-up. Support that `∑' (n : ℤ), ∥f n∥₊ * r ^ n` converges and is `≤ c`
(so in particular `f(T)` converges for `∥T∥ ≤ c`). Suppose also that
`∑' (n : ℤ), f n * 2⁻¹ ^ n = 0` (so `f` has a zero at `2⁻¹`; note that the sum
converges because `0 < 2⁻¹ < r`).

The conclusion is that `∑(n ≥ d) ∥∑(0≤i≤(n-d)) f(n - 1 - i)*2ⁱ∥ * r^n`
also converges and is bounded above by `c * (2 - r⁻¹)⁻¹`.

The power series `∑(n≥d) (∑(0≤i≤(n-d)) f(n - 1 - i)*2ⁱ) * Tⁱ` is the power
series of `f(T)/(T⁻¹-2)`, and the reason it behaves reasonsbly is the
assumption that T⁻¹-2 has a simple zero at 2⁻¹ and no other zeros in
the disc radius `r`.

### Implementation detail

In Lean the second sum is `∑' (n : ℤ), ∥ite (d ≤ n)`
  `((finset.range (n - d).nat_abs.succ).sum (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l))`
  `0∥₊ * r ^ n`.

### The maths proof

  ∑(n ≥ d) ∥∑(0≤i≤(n-d)) f(n - 1 - i)*2ⁱ∥ * r^n
= ∑(n ≥ d) ∥∑(i≥0) f(n - 1 - i)2ⁱ∥ * rⁿ (as f(n-1-i) vanishes for i larger than n-d)
= ∑(n ≥ d) ∥(i<0) f(n - 1 - i)2ⁱ∥ * rⁿ (as sum f(x)2⁻ˣ=0)
= ∑(n ≥ d) ∥∑(k≥0) f(n + k) 2^(-1-k)∥ * rⁿ (set k=-1-i)
≤ ∑(n ≥ d) ∑(k≥0)∥ f(n+k)∥ 2^(-1-k) r^n (Cauchy-Schwarz)
= ∑(k≥0) ∑(n≥d) ∥f(n+k)∥2^(-1-k)r^n (turns out you can interchange the sums)
= 2⁻¹∑(k≥0) (∑(n≥d) ∥f(n+k)∥r^(n+k)) * (2r)^{-k} (rearranging)
≤ 2⁻¹∑(k≥0) c (2r)^{-k} (defining property of c)
= 2⁻¹ * c / (1-(2r)⁻¹) (sum of a GP)
= c * (2-r⁻¹)⁻¹ (rearranging)

### Comments on the maths proof

The logic in this proof is completely standard but needs a little thinking about
when formalising. Some of the manipulations we are doing in the earlier lines
of the proof (for example interchanging the sums) are only valid if the sum converges.
However ultimately the proof that the sum converges only happens on the last-but-one
line of  the computation, where we prove that it's bounded above by something finite
(the sum of a GP).

There are several ways to fix this.

* One can go through the proof twice. In the first pass one can prove that everything
is `summable`, and then in the second pass one can then prove the results about equality
or boundedness of sums. This has the disadvantage that you have to do everything twice.

* Another approach is to write the proof once, but backwards; start with the sum of a geometric
progression and then go upwards through the maths proof above to deduce convergence and boundedness
of the original sum simultaneously. This has the mild disadvantage that you have to write
the proof backwards.

* A third approach would be to work not with `tsum` and `summable` at all, but to work
with `has_sum`. This has the disadvantage that you need to stop working with
equalities `∑a(n)=∑b(n)` or inequalities `∑a(n) ≤ ∑b(n)` and to start working with more complex
statements such as `has_sum a s ↔ has_sum b s` or `has_sum a s → ∃ t, has_sum b t ∧ t ≤ s`.

* The fourth approach avoids all of this. Instead of working with sums valued in `ℝ≥0` we
can work with sums taking values in `ℝ≥0∞` a.k.a. the interval `[0,∞]`.

## Lemma 2 (needed in part 4)

The second lemma states that if `z : ℝ` then one can find a power series
`f` in `ℤ⟦T⟧[T⁻¹]` such that `f 2⁻¹` converges to `z` and furthermore
such that all of the coefficients of `f` have absolute value at most 1.

## The maths proof.

The case `z=0` is easy, and for negative `z` one can just change sign,
so WLOG `0 < z`. In this case, che construction is algorithmic.
First find `d : ℤ` (the index where the power series will start)
such that `2⁻¹ ^ d ≤ z < 2⁻¹ ^ (d - 1)`. Now simply "write z in binary".

## TODO

Switch to ennreal and then prove 6 lemmas for the first result. All the
summability results are in `thm69` so it's simply a case of
refactoring all of them.

-/

lemma real.nnnorm_int (n : ℤ) : ∥(n : ℝ)∥₊ = ∥n∥₊ :=
subtype.ext $ by simp [coe_nnnorm, real.norm_eq_abs, int.norm_eq_abs]

-- do we want this? I'll use it here just to make things look a bit cleaner
noncomputable def nnreal.log (z : ℝ≥0) := (z : ℝ).log

-- definitely care about 0 < w < 1 so definitely care about negative logs
-- lemma is false if w = 1 and n = any and r = 0
-- lemma is false if w = 0 and n ≠ 0 and r = 2⁻¹
lemma nnreal.zpow_le_iff_log {w r : ℝ≥0} (hw : 0 < w) (hr : 0 < r) {n : ℤ} :
  w^n ≤ r ↔ w.log * n ≤ r.log :=
begin
  delta nnreal.log,
  rw [mul_comm, ←real.log_zpow],
  rw (show w ^ n ≤ r ↔ (w : ℝ) ^ n ≤ (r : ℝ), by norm_cast),
  rw real.log_le_log; norm_cast,
  { exact nnreal.zpow_pos hw.ne.symm _ },
  { exact hr },
end

-- lemma is false if w = 1 and n = any and r = 0
-- lemma is false if w = 0 and n ≠ 0 and r = 2⁻¹?
lemma nnreal.lt_zpow_iff_log {w r : ℝ≥0} (hw : 0 < w) (hr : 0 < r) {n : ℤ} :
  r < w ^ n ↔ r.log < w.log * n :=
begin
  delta nnreal.log,
  rw [mul_comm, ←real.log_zpow],
  rw real.log_lt_log_iff,
  { norm_cast },
  { assumption_mod_cast },
  { apply zpow_pos_of_pos,
    assumption_mod_cast },
end

lemma int.ceil_sub_one_lt {α : Type*} [linear_ordered_ring α] [floor_ring α]
(a : α) : (⌈a⌉ : α) - 1 < a :=
sub_lt_iff_lt_add.mpr (int.ceil_lt_add_one a)

namespace psi_aux_lemma1

/-

## The first lemma

-/

lemma key_tsum_lemma (f : ℤ → ℝ) (r : ℝ≥0) (hr1 : r < 1) (hr2 : 2⁻¹ < r) (d : ℤ)
  (hdf : ∀ n, n < d → f n = 0) (hconv : summable (λ n : ℤ, ∥f n∥₊ * r ^ n))
  (hzero : ∑' n, f n *  2⁻¹ ^ n = 0) :
∑' (n : ℤ), ∥ite (d ≤ n) ((finset.range (n - d).nat_abs.succ).sum
  (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l)) 0∥₊ * r ^ n ≤
  (2 - r⁻¹)⁻¹ * ∑' n, ∥f n∥₊ * r ^ n :=
begin
  sorry
end

end psi_aux_lemma1

/-

## The second lemma

-/

namespace psi_aux_lemma2

-- do I want z : ℝ≥0 here?
-- construction of C₄ function for z>0
noncomputable def C4_aux_function {z : ℝ≥0} (d : ℤ) (hd : 2⁻¹ ^ d ≤ z) (h' : z < 2⁻¹ ^ (d - 1)) :
ℕ → ℕ × ℝ≥0
| 0 := ⟨⌊z / (2⁻¹ ^ d)⌋₊, z - ⌊z / (2⁻¹ ^ d)⌋₊ * 2⁻¹ ^ d⟩
| (n + 1) := ⟨⌊(C4_aux_function n).2 / 2⁻¹⌋₊,
  (C4_aux_function n).2 - ⌊(C4_aux_function n).2 * 2⌋₊ * 2⁻¹⟩

lemma useful {z : ℝ} (hz : 0 < z) : ∃ d : ℤ, 2⁻¹ ^ d ≤ z.to_nnreal ∧ z.to_nnreal < 2⁻¹ ^ (d - 1) :=
begin
  use ⌈z.log / (2⁻¹ : ℝ).log⌉,
  split,
  { rw nnreal.zpow_le_iff_log (by norm_num : (0 : ℝ≥0) < 2⁻¹) (real.to_nnreal_pos.mpr hz),
    rw ← div_le_iff_of_neg',
    { convert int.le_ceil _,
      exact (real.coe_to_nnreal _ hz.le).symm },
    { apply real.log_neg; norm_num } },
  { rw nnreal.lt_zpow_iff_log (by norm_num : (0 : ℝ≥0) < 2⁻¹) (real.to_nnreal_pos.mpr hz),
    rw ← lt_div_iff_of_neg',
    { push_cast,
      convert int.ceil_sub_one_lt _,
      delta nnreal.log,
      rw real.coe_to_nnreal _ hz.le },
    { apply real.log_neg; norm_num } },
end

noncomputable def eval_half_inv (z : ℝ) : ℤ → ℤ :=
if hz0 : z = 0 then λ n, 0 else
if hz : 0 < z then (λ m, if m < (useful hz).some then 0 else (C4_aux_function (useful hz).some
  (useful hz).some_spec.1 (useful hz).some_spec.2 (m - (useful hz).some).nat_abs).1)
else if hz : 0 < -z then (λ m, if m < (useful hz).some then 0 else -(C4_aux_function (useful hz).some
  (useful hz).some_spec.1 (useful hz).some_spec.2 (m - (useful hz).some).nat_abs).1)
else 37 -- never get here

-- Needed for a later bound
lemma abs_le_one (z : ℝ) (n : ℤ) : ∥eval_half_inv z n∥₊ ≤ 1 := sorry

-- needed for definition of missing data (definition of splitting of eval(1/2) map).
-- Proof is "∥f n∥ ≤ 1 always and = 0 for `n<d` so bounded by sum of a GP".
lemma summable (z : ℝ) {r : ℝ≥0} (hr : r < 1) :
summable (λ n : ℤ, ∥eval_half_inv z n∥₊ * r ^ n) := sorry

-- We'll figure out what we need right now.
lemma tsum_le (z : ℝ) {r : ℝ≥0} : ∑' n, ∥eval_half_inv z n∥₊ * r ^ n ≤ ∥z∥₊ * (1 - r)⁻¹ :=
begin
  have foo : ∀ (n : ℤ), ∥eval_half_inv z n∥₊ * r ^ n ≤ r ^ n := λ n,
    mul_le_of_le_one_left (zero_le (r ^ n)) (abs_le_one z n),

end

lemma tsum_half (z : ℝ) : ∑' n, (eval_half_inv z n : ℝ) * 2⁻¹ ^ n = z := sorry

end psi_aux_lemma2
