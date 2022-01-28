-- import topology.algebra.infinite_sum
import data.finset.nat_antidiagonal
import analysis.normed_space.basic

open metric --finset --filter
open_locale nnreal classical big_operators topological_space

namespace aux_thm69

section equivalences

-- def nat_lt_nat := { x : ℕ × ℕ // x.snd < x.fst }
-- local notation `𝒮` := nat_lt_nat

-- lemma summable.summable_on_𝒮 (f g : ℕ → ℝ) (hf : summable (λ n, ∥ f n ∥))
--   (hg : summable (λ n, ∥ g n ∥)) : summable (λ x : ℕ × ℕ, f (x.fst + 1 + x.snd) * g (x.snd)) :=
-- begin
--   sorry
-- end

end equivalences

section summable

lemma goofy {r : ℝ≥0} (f : ℤ → ℤ) (hf : summable (λ n, ∥ f n ∥ * r ^ n)) (b : ℕ)
: (λ n : ℕ, (2 * r : ℝ) ^ n * ∥∑' (x : ℕ), (1 / 2 : ℝ) ^ (n + x + 1 : ℤ) * (f (n + x + 1 : ℤ))∥) b ≤
  (λ n : ℕ, (2 * r : ℝ) ^ n * ∥∑' (x : ℕ), (1 / 2 : ℝ) ^ (x + 1) * (f (x + 1))∥) b:=
begin
  sorry,
end

lemma aux_pos_terms {r : ℝ≥0} (f : ℤ → ℤ) (n : ℕ) : 0 ≤ (2 * r : ℝ) ^ n *
  ∥∑' (x : ℕ), (1 / 2 : ℝ) ^ (n + x + 1) * ↑(f (n + 1 + x))∥ := sorry

lemma summable_convolution {r : ℝ≥0} (hr₀: 0 < r) (f : ℤ → ℤ) (d : ℤ)
  (hf : summable (λ n, ∥ f n ∥ * r ^ n)) (hd : ∀ n : ℤ, n < d → f n = 0) :
  summable (λ n : ℤ, (1 / 2) * ∥ tsum (λ i : ℕ, ((f (n + 1 + i)) : ℝ) * (1 / 2) ^ i) ∥ * r ^ n) :=
begin
  -- sorry;{

  suffices h_on_nat : summable (λ (n : ℕ),
    (1 / 2) * ∥∑' (i : ℕ), (1 / 2 : ℝ) ^ i * (f (n + 1 + i))∥ * (r : ℝ) ^ n),
  { sorry -- this is the switch from nat to int
    },

  { have half_norm : (1 / 2 : ℝ) = ∥ (1 / 2  : ℝ) ∥, sorry,
    rw half_norm,
    simp_rw [mul_comm, ← normed_field.norm_mul, ← tsum_mul_left, ← mul_assoc],
    rw ← half_norm,
    simp_rw [← (pow_succ (1 / 2 : ℝ) _)],
    convert_to summable (λ (n : ℕ), ((2 : ℝ) * r) ^ n * ∥∑' (x : ℕ), (1 / 2 : ℝ) ^ (n + x + 1 : ℤ)
      * (f (n + 1 + x))∥),
    { funext n,
      nth_rewrite_rhs 0 [mul_pow],
      nth_rewrite_rhs 1 [mul_comm],
      nth_rewrite_rhs 0 [mul_assoc],
      rw mul_eq_mul_left_iff,
      apply or.intro_left,
      nth_rewrite_rhs 0 [← inv_inv₀ (2 : ℝ)],
      nth_rewrite_rhs 0 [← zpow_neg_one],
      nth_rewrite_rhs 0 [← zpow_of_nat],
      nth_rewrite_rhs 0 [← zpow_mul₀],
      nth_rewrite_rhs 0 [inv_eq_one_div],
      rw [neg_one_mul, int.of_nat_eq_coe, half_norm, ← normed_field.norm_zpow,
        ← normed_field.norm_mul ((1 / 2 : ℝ) ^ (- ↑n)) _, ← half_norm],
      simp_rw [← tsum_mul_left, ← mul_assoc, ← zpow_add₀ $ one_div_ne_zero $ @two_ne_zero ℝ _ _, add_assoc,
        neg_add_cancel_left],
      refl },
      -- let g := λ b : ℕ, (2 * r : ℝ) ^ b * ∥∑' (x : ℕ), (1 / 2 : ℝ) ^ (↑x + 1) * f (1 + ↑x)∥,
      have := @summable_of_nonneg_of_le _ _ _ _ (goofy f hf),
      simp only at this,
      apply this,
      apply summable_of_nonneg_of_le,
      { intro b, exact aux_pos_terms f b},
      { intro b,
        have : (0 : ℝ) < (2 * ↑r) ^ b,
        { apply pow_pos,
          apply mul_pos,
          simp only [zero_lt_bit0, zero_lt_one],
          simpa only [nnreal.coe_pos],},
      simp only [one_div] },
      -- squeeze_simp [(mul_le_mul_left this).mpr (goofy f hf b)],
      -- have fine := (mul_le_mul_left this).mpr (goofy f hf b),
      -- simp only at fine },



      suffices : summable (λ (n : ℕ), (2 * ↑r) ^ n * ∥∑' (x : ℕ), (1 / 2) ^ (↑x + 1) *
        (f (1 + ↑x))∥),
      sorry,-- **[FAE]** this is a reduction to a subtype, and it has already been proven
      --somewhere as aux lemma


      have H1 : summable (λ x : ℕ, (1 / 2 : ℝ) ^ (x + 1 : ℤ) * (f (1 + x) : ℝ)), sorry,
      replace H1 := H1.has_sum,
      have H2 : summable (λ n : ℕ, (2 * r : ℝ) ^ n), sorry,
      replace H2 := H2.has_sum,
      have H3 := H2.mul_eq H1,
      --hf.has_sum.mul_eq hg.has_sum hfg.has_sum

      -- **[FAE]** Now it is the product of a convergent geometric series and a convergent gadget
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



  -- }
end

end summable

section tsum

end tsum

end aux_thm69
