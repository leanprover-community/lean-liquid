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

open_locale ennreal

-- line 5 ≤ line 10
lemma step6 {f : ℤ → ℝ} {d : ℤ} {r : ℝ≥0} (hr2 : 2⁻¹ < r) (hdf : ∀ n, n < d → f n = 0)
  (hconv : summable (λ n : ℤ, ∥f n∥₊ * r ^ n)) :
(2⁻¹ : ℝ≥0∞) * ∑' (i j : ℕ), ↑∥f (d + ↑i + ↑j) * 2⁻¹ ^ j∥₊ * ↑(r ^ (d + ↑i)) ≤
  ↑(2 - r⁻¹)⁻¹ * ∑' (a : ℤ), ↑(∥f a∥₊ * r ^ a) :=
begin
  rw ennreal.tsum_comm,
  -- woohoo, I just interchanged the sums
  sorry
end

lemma step5 {f : ℤ → ℝ} {d : ℤ} {r : ℝ≥0} (hr2 : 2⁻¹ < r) (hdf : ∀ n, n < d → f n = 0)
  (hconv : summable (λ n : ℤ, ∥f n∥₊ * r ^ n)) :
  summable (λ (x : ℤ), f x * 2⁻¹ ^ x) :=
begin
  rw ← summable_subtype_and_compl,
  change summable (λ x : {n : ℤ | n < 0}, _) ∧ _,
  split,
  { let F : finset ↥{n : ℤ | n < 0} := finset.preimage (finset.Ico d 0 : finset ℤ) coe
    (set.inj_on_of_injective subtype.coe_injective _),
    apply summable_of_ne_finset_zero,
    rintro b (hb : b ∉ F),
    convert zero_mul _,
    apply hdf,
    by_contra hbd, push_neg at hbd,
    apply hb,
    rw finset.mem_preimage,
    rw finset.mem_Ico,
    exact ⟨hbd, b.2⟩ },
  { apply summable_of_summable_nnnorm,
    have := nnreal.summable_subtype hconv {n : ℤ | n < 0}ᶜ,
    refine nnreal.summable_of_le _ this,
    rintro ⟨b, hb : ¬ b < 0⟩,
    push_neg at hb,
    rw nnnorm_mul,
    suffices : ∥f b∥₊ * (2 ^ b)⁻¹ ≤ ∥f b∥₊ * r ^ b,
    { simpa },
    apply nnreal.mul_le_mul_left,
    rw ← inv_zpow₀,
    apply nnreal.zpow_le_zpow' hb hr2.le, },
end
example (r : ℝ≥0) (n : ℕ) : r ^ (n : ℤ) = r ^ n := zpow_coe_nat r n
noncomputable instance xxx : div_inv_monoid ℝ≥0 := infer_instance

--lemma zpow_
lemma step4 {f : ℤ → ℝ} {n d : ℤ} {r : ℝ≥0} (hr1 : r < 1) (hr2 : 2⁻¹ < r)
  (hdf : ∀ n, n < d → f n = 0)
  (hconv : summable (λ n : ℤ, ∥f n∥₊ * r ^ n)) (hzero : ∑' n, f n *  2⁻¹ ^ n = 0) :
  ∑' (l : ℕ), f (n - 1 - ↑l) * 2 ^ l =  2⁻¹ * -∑' (m : ℕ), f (n + m) * 2⁻¹ ^ m :=
begin
  have : ∀ l : ℕ, (2 : ℝ) ^ l = 2⁻¹ ^ (n - 1 - l) * (2⁻¹ * 2 ^ n),
  { intro l,
    rw [inv_zpow₀, ← zpow_neg₀, ← zpow_neg_one, ← zpow_coe_nat],
    push_cast,
    rw ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0),
    rw ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0),
    ring_nf, },
  conv_lhs begin
    congr,
    funext,
    rw [this, ← mul_assoc],
  end, clear this,
  rw tsum_mul_right,
  have : ∀ m : ℕ, (2⁻¹ : ℝ) ^ m = 2⁻¹ ^ (n + m) * 2 ^ n,
  { intro m,
    rw [inv_zpow₀, ← zpow_neg₀, ← zpow_coe_nat, ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0),
      inv_zpow₀, ← zpow_neg₀],
    ring_nf, },
  conv_rhs begin
    congr, skip,
    congr,
    congr,
    funext,
    rw [this, ← mul_assoc],
  end, clear this,
  rw [mul_comm, mul_assoc, tsum_mul_right, ← neg_mul, mul_comm ((2 : ℝ) ^ n)],
  congr,
  apply eq_neg_of_add_eq_zero,
  rw [add_comm, ← hzero],
  rw ← tsum_add_tsum_compl ((step5 hr2 hdf hconv).comp_injective subtype.coe_injective :
    summable ((_ : ℤ → ℝ) ∘ (coe : {z : ℤ | n ≤ z} → ℤ)))
    ((step5 hr2 hdf hconv).comp_injective subtype.coe_injective),
  { congr' 1,
    { rw ← ((nat.equiv_le_int n).tsum_eq : _ → (_ : ℝ) = _),
      congr', ext b,
      rw add_comm n,
      refl, },
    { rw ← ((nat.equiv_le_int_compl n).tsum_eq : _ → (_ : ℝ) = _),
      congr', ext b,
      rw (show n - 1 - b = n - (b + 1), by ring),
      refl, } },
end

-- second line ≤ last line
lemma step3 {f : ℤ → ℝ} {r : ℝ≥0} (hr1 : r < 1) (hr2 : 2⁻¹ < r) {d : ℤ}
  (hdf : ∀ n, n < d → f n = 0) (hconv : summable (λ n : ℤ, ∥f n∥₊ * r ^ n))
  (hzero : ∑' n, f n *  2⁻¹ ^ n = 0) :
∑' (n : ℤ), ((∥ite (d ≤ n) (∑' (l : ℕ), f (n - 1 - ↑l) * 2 ^ l) 0∥₊ * r ^ n : ℝ≥0) : ℝ≥0∞) ≤
  ((2 - r⁻¹)⁻¹ * ∑' (n : ℤ), ∥f n∥₊ * r ^ n : ℝ≥0) :=
begin
  simp_rw step4 hr1 hr2 hdf hconv hzero,
  -- n - d = m
  rw tsum_eq_tsum_of_ne_zero_bij (λ m : function.support
  (λ m : ℕ, ((∥(2⁻¹ : ℝ) * (-∑' (l : ℕ), f (d + m + ↑l) * 2⁻¹ ^ l)∥₊ * r ^ (d + m) : ℝ≥0) : ℝ≥0∞)),
  d + m.1),
  { dsimp only,
    simp_rw [nnnorm_mul, nnnorm_neg],
    push_cast,
    simp only [nnnorm_inv, real.nnnorm_two, ennreal.coe_inv, ne.def, bit0_eq_zero, one_ne_zero,
      not_false_iff, ennreal.coe_bit0, ennreal.coe_one],
    have summable_half : ∀ t : ℤ, summable (λ (x : ℕ), f (t + ↑x) * 2⁻¹ ^ x),
    { intro t,
      rw summable_mul_right_iff (show (2 : ℝ)⁻¹ ^ t ≠ 0, from zpow_ne_zero _ (by norm_num)),
      simp_rw [mul_assoc, ← zpow_coe_nat],
      simp_rw [← zpow_add₀ (show (2 : ℝ)⁻¹ ≠ 0, by norm_num), add_comm _ t],
      exact (step5 hr2 hdf hconv).comp_injective (show function.injective (λ x : ℕ, t + x),
      by {intros x y hxy, simpa using hxy, }), },
    suffices :
      ∑' (m : ℕ), (2⁻¹ : ℝ≥0∞) * ↑(∑' (l : ℕ), ∥f (d + ↑m + ↑l) * (2⁻¹ ^ l)∥₊ : ℝ≥0) *
        ↑(r ^ (d + ↑m)) ≤ ↑(2 - r⁻¹)⁻¹ * ↑∑' (n : ℤ), ∥f n∥₊ * r ^ n,
    { refine le_trans _ this,
      apply ennreal.tsum_le_tsum,
      intro m,
      apply ennreal.mul_le_mul_of_right,
      apply ennreal.mul_le_mul_of_left,
      norm_cast,
      apply nnnorm_tsum_le,
      rw ← nnreal.summable_iff_summable_nnnorm,
      apply summable_half, },
    rw ennreal.coe_tsum hconv, dsimp only,
    conv_lhs begin
      congr,
      funext,
      rw ennreal.coe_tsum (show summable (λ (l : ℕ), ∥f (d + m + ↑l) * 2⁻¹ ^ l∥₊), begin
      rw ← nnreal.summable_iff_summable_nnnorm,
      apply summable_half, end),
    end,
    dsimp only,
    simp_rw mul_assoc,
    rw ennreal.tsum_mul_left,
    simp_rw ← ennreal.tsum_mul_right,
    apply step6 hr2 hdf hconv, },
  { rintro ⟨x, _⟩ ⟨y, _⟩ h,
    have hxy : x = y,
    { simpa using h },
    subst hxy },
  { rintro n hn,
    rw function.mem_support at hn,
    split_ifs at hn with hdn,
    { rw set.mem_range,
      let m := (n - d).nat_abs,
      have hm : d + m = n,
      { apply add_eq_of_eq_sub',
        rw [int.nat_abs_of_nonneg],
        exact sub_nonneg.mpr hdn, },
      refine ⟨⟨m, _⟩, hm⟩,
      rw function.mem_support,
      convert hn,
      rw hm, },
    { exfalso,
      apply hn,
      simp, } },
  { simp, },
end


-- first line equals second line
lemma step2 {f : ℤ → ℝ} {n d : ℤ} (hn : d ≤ n) (hdf : ∀ n, n < d → f n = 0) :
  (finset.range (n - d).nat_abs.succ).sum (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l) =
  ∑' (l : ℕ), f (n - 1 - l) * 2 ^ l :=
begin
  apply (tsum_eq_sum _ : (_ : ℝ) = _).symm,
  intros b hb,
  convert zero_mul ((2 : ℝ) ^ b),
  apply hdf,
  by_contra hbd,
  push_neg at hbd,
  apply hb,
  rw [finset.mem_range, nat.lt_succ_iff],
  suffices : (b : ℤ) ≤ ((n - d).nat_abs : ℤ),
  { assumption_mod_cast, },
  rw ← int.eq_nat_abs_of_zero_le;
  linarith,
end

-- coerce to ℝ≥0∞
lemma step1 {f : ℤ → ℝ} {r : ℝ≥0} (hr1 : r < 1) (hr2 : 2⁻¹ < r) {d : ℤ}
  (hdf : ∀ n, n < d → f n = 0) (hconv : summable (λ n : ℤ, ∥f n∥₊ * r ^ n))
  (hzero : ∑' n, f n *  2⁻¹ ^ n = 0) :
∑' (n : ℤ),
    ((∥ite (d ≤ n) ((finset.range (n - d).nat_abs.succ).sum (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l)) 0∥₊ *
      r ^ n : ℝ≥0) : ℝ≥0∞) ≤
  ((2 - r⁻¹)⁻¹ * ∑' (n : ℤ), ∥f n∥₊ * r ^ n : ℝ≥0) :=
begin
  have : ∀ n,
  ∥ite (d ≤ n) ((finset.range (n - d).nat_abs.succ).sum (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l)) 0∥₊ * r ^ n
  =
  ∥ite (d ≤ n) (∑' (l : ℕ), f (n - 1 - l) * 2 ^ l) 0∥₊ * r ^ n,
  { intro n,
    congr' 2,
    split_ifs with hn,
    { rw step2 hn hdf },
    { refl } },
  simp_rw this,
  apply step3 hr1 hr2 hdf hconv hzero,
end

-- first line ≤ last line
lemma key_tsum_lemma (f : ℤ → ℝ) (r : ℝ≥0) (hr1 : r < 1) (hr2 : 2⁻¹ < r) (d : ℤ)
  (hdf : ∀ n, n < d → f n = 0) (hconv : summable (λ n : ℤ, ∥f n∥₊ * r ^ n))
  (hzero : ∑' n, f n *  2⁻¹ ^ n = 0) :
∑' (n : ℤ), ∥ite (d ≤ n) ((finset.range (n - d).nat_abs.succ).sum
  (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l)) 0∥₊ * r ^ n ≤
  (2 - r⁻¹)⁻¹ * ∑' n, ∥f n∥₊ * r ^ n :=
begin
  have := step1 hr1 hr2 hdf hconv hzero,
  have this2 : ∑' (n : ℤ),
  (((∥ite (d ≤ n) ((finset.range (n - d).nat_abs.succ).sum (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l)) 0∥₊ *
       r ^ n) : ℝ≥0) : ℝ≥0∞) < ⊤,
  { refine lt_of_le_of_lt this _,
    exact ennreal.coe_lt_top,
  },
  have this3 : summable (λ n, ((∥ite (d ≤ n) ((finset.range (n - d).nat_abs.succ).sum (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l)) 0∥₊ *
       r ^ n) : ℝ≥0)) := ennreal.tsum_coe_ne_top_iff_summable.mp this2.ne,
  rw ← ennreal.coe_le_coe,
  convert this,
  apply ennreal.coe_tsum this3,
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

namespace theta_aux_lemma

-- Here is the fact which Clausen/Scholze need for the application to "splitting θ
-- in a bounded way".

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
