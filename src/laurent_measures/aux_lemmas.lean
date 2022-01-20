-- import topology.algebra.infinite_sum
import data.finset.nat_antidiagonal
import analysis.normed_space.basic

open metric --finset --filter
open_locale nnreal classical big_operators topological_space

namespace aux_thm69

section equivalences

def nat_lt_nat := { x : ℕ × ℕ // x.snd < x.fst }
local notation `𝒮` := nat_lt_nat

lemma summable.summable_on_𝒮 (f g : ℕ → ℝ) (hf : summable (λ n, ∥ f n ∥))
  (hg : summable (λ n, ∥ g n ∥)) : summable (λ x : ℕ × ℕ, f (x.fst + 1 + x.snd) * g (x.snd)) :=
begin
  sorry
end

end equivalences

section summable

-- example (x : ℝ) (a : ℕ) : x * x ^ a = x ^(a+1):= by library_search

lemma summable_convolution {r : ℝ≥0} (f : ℤ → ℤ) (d : ℤ) (hf : summable (λ n, ∥ f n ∥ * r ^ n)) (hd : ∀ n : ℤ, n < d → f n = 0) :
  summable (λ n : ℤ, (1 / 2) * ∥ tsum (λ i : ℕ, ((f (n + 1 + i)) : ℝ) * (1 / 2) ^ i) ∥ * r ^ n) :=
begin
  sorry;{

  suffices h_on_nat : summable (λ (n : ℕ),
    (1 / 2) * ∥∑' (i : ℕ), (1 / 2 : ℝ) ^ i * (f (n + 1 + i))∥ * (r : ℝ) ^ n),
  { sorry -- this is the switch from nat to int
    },
  -- simp_rw [mul_comm],

  { have uno : (1 / 2 : ℝ) = ∥ (1 / 2  : ℝ) ∥, sorry,
    -- have due : (1 / 2 : ℝ) ≠ 0 , sorry,
    simp_rw [mul_comm],
    -- simp_rw [mul_comm],
    rw uno,
    simp_rw [← normed_field.norm_mul],
    simp_rw [← tsum_mul_left, ← mul_assoc],
    rw ← uno,
    -- simp_rw [mul_comm (1 / 2 : ℝ) _],
    simp_rw [← (pow_succ (1 / 2 : ℝ) _)],
   -- ***[FAE]*** Now: insert n in the exponent and take it out of the ∥ - ∥

    -- have h_bdd : ∀ n : ℕ, ∥ tsum (λ i : ℕ, (1 / 2) ^ i * (f (n + 1 + i))) ∥ ≤
    -- ∥ tsum (λ i : ℕ, (1 / 2) ^ i * (f (1 + i))) ∥,
    -- {},
    -- replace h_bdd : ∀ n : ℕ, ∥ tsum (λ i : ℕ, (r : ℝ) ^ n * ( 1 / 2) * (1 / 2) ^ i * (f (n + 1 + i))) ∥ ≤
    --   ∥ (r : ℝ) ^ n * ( 1 / 2) * tsum (λ i : ℕ, (1 / 2) ^ i * (f (1 + i))) ∥, sorry,
    -- replace h_bdd : ∀ n : ℕ, (r : ℝ) ^ n * ( 1 / 2) * ∥ tsum (λ i : ℕ, (1 / 2) ^ i * (f (n + 1 + i))) ∥ ≤ (r : ℝ) ^ n * ( 1 / 2) * ∥ tsum (λ i : ℕ, (1 / 2) ^ i * (f (1 + i))) ∥, sorry,
    -- apply summable_of_nonneg_of_le _ h_bdd,
    -- apply @summable.mul_right _ _ _ _ _ (λ n : ℕ, (r : ℝ) ^ n * ( 1 / 2))
    -- (∥ ∑' (i : ℕ), (1 / 2) ^ i * (f (1 + i)) ∥),
    -- apply summable.mul_right,
    -- sorry,--this is just the sum of the geometric series
    -- sorry,--trivial, product of positive gadgets
  },



  }
end

end summable

section tsum

end tsum

end aux_thm69
