import data.real.nnreal
import topology.algebra.infinite_sum
import topology.instances.ennreal
import topology.algebra.monoid

open_locale nnreal big_operators
open finset

/-!

# A technical lemma on the way to `lem98`

The purpose of this file is to prove the following lemma:
```
lemma exists_partition (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (hf' : summable f) :
  ∃ (mask : fin N → set ℕ),
    (∀ n, ∃! i, n ∈ mask i) ∧ (∀ i, ∑' n, set.indicator (mask i) f n ≤ (∑' n, f n) / N + 1) :=
```
In disguise, this is `lem98` (`combinatorial_lemma/default.lean`) specialized to `Λ = ℤ`.
The proof of the general case makes a reduction to this special case.

## Informal explanation of the statement

The lemma `exists_partition` informally says the following:

Suppose we have a sequence of real numbers `f 0`, `f 1`, …, all between `0` and `1`,
and suppose that `c = ∑ (f i)` exists.
Then, for every positive natural number `N`, we can split `f` into `N` subsequences `g 1`, …, `g N`,
such that `∑ (g j i) ≤ c/N + 1`.

The informal proof is easy: consider `N` buckets, that are initially empty.
Now view the numbers `f i` as an incoming stream of numbers,
and place each of these in the buckets with the smallest total sum.

The formal proof is a bit trickier: we need to make sure that every number ends up in a bucket,
we need to show that the final subsequences have a converging sum, etc…
We model the subsqeuences by using indicator functions to mask parts of `f`
using `N` subsets of `ℕ` (`mask` in the statement).

In `recursion_data` below, we setup the `N` buckets,
and define the recursion step in `recursion_data_succ`.
The rest of the file consists of assembling the pieces.

-/

namespace combinatorial_lemma

/-- A data structure for recording partial sums of subsequences of a sequence of real numbers,
such that all the partial sums are rougly the same size.
The field `m` records to which partial sum the next entry in the sequence will be added. -/
structure recursion_data (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (k : ℕ) :=
(m : fin N → Prop)
(hm : ∃! i, m i)
(partial_sums : fin N → ℝ≥0)
(h₁ : ∑ i, partial_sums i = ∑ n in range (k + 1), f n)
(h₂ : ∀ i, partial_sums i ≤ (∑ n in range (k + 1), f n) / N + 1)
[dec_inst : ∀ i, decidable (m i)]

attribute [instance] recursion_data.dec_inst

/-- The starting point for recursively constructing subsequences of a sequence of real numbers
such that all the subsequences sum to be roughly the same size:
we start by placing the first element of the sequence into the subsequence `0`. -/
def recursion_data_zero (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) :
  recursion_data N hN f hf 0 :=
{ m := λ j, j = ⟨0, hN⟩,
  hm := ⟨_, rfl, λ _, id⟩,
  partial_sums := λ j, if j = ⟨0, hN⟩ then f 0 else 0,
  h₁ := by simp only [sum_ite_eq', if_true, mem_univ, sum_singleton, range_one],
  h₂ :=
  begin
    intros i,
    split_ifs,
    { simp only [sum_singleton, range_one],
      refine (hf 0).trans _,
      exact self_le_add_left 1 (f 0 / ↑N) },
    { exact zero_le' }
  end }

instance (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) :
  inhabited (recursion_data N hN f hf 0) := ⟨recursion_data_zero N hN f hf⟩

/-- Given partial sums of subsequences up to the `k`-th element in a sequence of real numbers,
add the `k+1`st element to the smallest partial sum so far. -/
noncomputable def recursion_data_succ (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (k : ℕ)
  (dat : recursion_data N hN f hf k) :
  recursion_data N hN f hf (k + 1) :=
let I := (finset.univ : finset (fin N)).exists_min_image
  dat.partial_sums ⟨⟨0, hN⟩, finset.mem_univ _⟩ in
{ m := λ j, j = I.some,
  hm := ⟨I.some, rfl, λ _, id⟩,
  partial_sums := λ i, dat.partial_sums i + (if i = I.some then f (k + 1) else 0),
  h₁ :=
  begin
    rw sum_range_succ _ (k + 1),
    simp [finset.sum_add_distrib, dat.h₁, add_comm],
  end,
  h₂ :=
  begin
    intros i,
    split_ifs,
    { rw h,
      have : dat.partial_sums I.some * N ≤ (∑ n in range (k + 1 + 1), f n),
      { calc dat.partial_sums I.some * N
            = ∑ i : fin N, dat.partial_sums I.some : _
        ... ≤ ∑ i, dat.partial_sums i : _ -- follows from I
        ... = ∑ n in range (k + 1), f n : dat.h₁
        ... ≤ ∑ n in range (k + 1 + 1), f n : _,
        { simp only [finset.sum_const, finset.card_fin, nsmul_eq_mul, mul_comm] },
        { obtain ⟨-, HI⟩ := I.some_spec,
          apply finset.sum_le_sum,
          intros j hj, exact HI j hj },
        { rw sum_range_succ _ (k + 1),
          simp } },
      have : dat.partial_sums I.some ≤ (∑ n in range (k + 1 + 1), f n) / ↑N,
      { rwa nnreal.le_div_iff_mul_le, exact_mod_cast hN.ne' },
      exact add_le_add this (hf (k + 1)) },
    { calc dat.partial_sums i + 0
          ≤ (∑ n in range (k + 1), f n) / ↑N + 1 : by simpa using dat.h₂ i
      ... ≤ (∑ n in range (k + 1 + 1), f n) / ↑N + 1 : add_le_add _ le_rfl,
      simp only [div_eq_mul_inv, fin.sum_univ_eq_sum_range],
      refine mul_le_mul' _ le_rfl,
      simp only [finset.sum_range_succ],
      exact self_le_add_right _ _ }
  end }

/-- Recursively construct subsequences of a given sequence of real numbers,
in such a way that the sums of the subsequences are all roughly of the same size. -/
noncomputable def partition (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) :
  Π i : ℕ, (recursion_data N hN f hf i)
| 0 := recursion_data_zero N hN f hf
| (k + 1) := recursion_data_succ N hN f hf k (partition k)

lemma partition_sums_aux (k : ℕ) (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1)
  (i : fin N) :
  (partition N hN f hf (k + 1)).partial_sums i =
  (partition N hN f hf k).partial_sums i +
    if (partition N hN f hf (k + 1)).m i then f (k + 1) else 0 :=
by simp [partition, recursion_data_succ]

lemma partition_sums (k : ℕ) (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1)
  (i : fin N) :
  (partition N hN f hf k).partial_sums i =
    ∑ n in range (k + 1), set.indicator {k | (partition N hN f hf k).m i} f n :=
begin
  induction k with k IH,
  { dsimp [partition], simp, dsimp [partition, recursion_data_zero], congr },
  rw [partition_sums_aux, IH, sum_range_succ _ k.succ, set.indicator, add_right_inj],
  congr' 1,
end

lemma exists_partition (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (hf' : summable f) :
  ∃ (mask : fin N → set ℕ),
    (∀ n, ∃! i, n ∈ mask i) ∧ (∀ i, ∑' n, set.indicator (mask i) f n ≤ (∑' n, f n) / N + 1) :=
begin
  let mask : fin N → ℕ → Prop := λ i, {n | (partition N hN f hf n).m i},
  have h_sum : ∀ k i, ∑ n in range k, set.indicator (mask i) f n ≤ (∑ n in range k, f n) / N + 1,
  { rintros ⟨k⟩ i,
    { simp [mask] },
    rw ← partition_sums k N hN f hf i,
    exact (partition N hN f hf k).h₂ i, },
  refine ⟨mask, _, _⟩,
  { intros n, exact (partition N hN f hf n).hm },
  { intros i,
    set S₁ : ℝ≥0 := ∑' (n : ℕ), f n,
    have hf'' : has_sum f S₁ := hf'.has_sum,
    have hf''' : has_sum _ (S₁ / N) := hf''.mul_right (N:ℝ≥0)⁻¹,
    have : set.indicator (mask i) f ≤ f,
    { intros n,
      dsimp [set.indicator],
      split_ifs, exacts [le_rfl, zero_le'] },
    obtain ⟨S₂, -, h_mask⟩ := nnreal.exists_le_has_sum_of_le this hf'',
    rw h_mask.tsum_eq,
    rw nnreal.has_sum_iff_tendsto_nat at hf''' h_mask,
    have := filter.tendsto.add_const 1 hf''',
    apply le_of_tendsto_of_tendsto' h_mask this,
    intros n,
    simp only [div_eq_mul_inv, finset.sum_mul] at h_sum ⊢,
    exact h_sum n i }
end

end combinatorial_lemma

#lint-
