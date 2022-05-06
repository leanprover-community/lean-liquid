import data.real.nnreal
import topology.algebra.infinite_sum
import analysis.normed_space.basic
import for_mathlib.nnreal
import for_mathlib.nnreal_int_binary -- basic binary expansion for nnreal.

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
converges because `0 ≤ 2⁻¹ < r`).

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
We need some other basic results about such sequences but this
is the main one.

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

lemma real.neg_nnnorm_of_neg {r : ℝ} (hr : r < 0) : -(∥r∥₊ : ℝ) = r :=
by rw [coe_nnnorm, neg_eq_iff_neg_eq, real.norm_eq_abs, abs_of_neg hr]

namespace psi_aux_lemma

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
/-

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
-/
-- a Lean proof is embedded in the calculations in `laurent_measures/thm69.lean`
-- between lines 275 and 600 or so: see `psi_def_summable`, `psi_def_summable2`,
-- `psi_def_summable3`, `psi_def_aux_4`, `psi_def_aux_3`, `psi_def_aux_2`,
-- `psi_def_aux` and the `summable'` field in the definition of `ψ`.
-- These are the `summable` versions; we just need to beef everything up
-- to `tsum` versions, which will probably be easier in `ennreal`.

end psi_aux_lemma

/-

## The second lemma

-/

example (a b : ℤ) (ha : 0 < a) : b - a < b := sub_lt_self b ha

namespace theta_aux_lemma

-- Here is the fact which Clausen/Scholze need for the application to "splitting θ
-- in a bounded way".
-- proof: bounded above by sum of a GP

theorem tsum_le (r : ℝ≥0) {s : ℝ≥0} (hs0 : 0 < s) (hs : s < 1) :
∑' (n : ℤ), (nnreal.int.binary r n : ℝ≥0) * s ^ n ≤
  s ^ ⌈real.log r / real.log (2⁻¹ : ℝ≥0)⌉ * (1 - s)⁻¹ :=
begin
  let d := ⌈real.log r / real.log (2⁻¹ : ℝ≥0)⌉,
  rw mul_comm,
  rw ← nnreal.int.tsum_add_tsum_compl' {n : ℤ | n < d} (nnreal.int.binary_summable r hs),
  have h0 : ∑' (x : ↥{n : ℤ | n < d}), (λ (n : ℤ), ↑(nnreal.int.binary r n) * s ^ n) ↑x = 0,
  { convert (tsum_zero : _ = (0 : ℝ≥0)), ext ⟨n, hn : n < d⟩,
    simp [nnreal.int.binary_eq_zero r n hn] },
  rw [h0, zero_add], clear h0,
  rw ← (nat.equiv_int_lt_compl d).tsum_eq, swap, apply_instance,
  simp only [nat.equiv_int_lt_compl, zpow_add₀ hs0.ne', ←mul_assoc, equiv.coe_fn_mk, subtype.coe_mk,
    zpow_coe_nat, nonneg.coe_one, nnreal.tsum_mul_right],
  rw mul_le_mul_right₀ (zpow_ne_zero _ hs0.ne'),
  rw ← tsum_geometric_nnreal hs,
  refine nnreal.tsum_le_tsum (λ n, _) (nnreal.summable_geometric hs),
  apply mul_le_of_le_one_left',
  norm_cast,
  apply nnreal.int.binary_le_one,
end

end theta_aux_lemma

-- is `summable_subtype_and_compl` true for add_comm_monoids? Why is it stated for groups?
