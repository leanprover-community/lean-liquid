-- import for_mathlib.short_exact_sequence
import data.int.interval
import data.finset.nat_antidiagonal
import laurent_measures.basic
import laurent_measures.theta
import linear_algebra.basic


/-
This file introduces the maps
* `θ`, which is the specialization of evaluation-at-ξ map `ϑ` from `laurent_measures.theta`
  at `ξ=1/2`.
* `ϕ` which corresponds to multiplying a Laurent series in `ℒ S = (laurent_measures r S)`
  for `r = 2^(1/p)` by `2T-1`.
* `ψ` corresponds to multiplying a Laurent series by `(2T-1)^-1`. It is defined only on series
  vanishing at `1/2`, so that it again takes values in `ℒ S`
* The maps `Θ`, `Φ` and `Ψ` are the "measurifications" of `θ`, `ϕ` and `ψ`,
  so they are morphisms in the right category.

**The main results are ...**
-/

noncomputable theory

open nnreal theta laurent_measures finset
open_locale nnreal classical big_operators topological_space

section thm69

parameter {p : ℝ≥0}
def r : ℝ≥0 := (1 / 2) ^ ( 1 / p.1)
variables [fact(0 < p)] [fact (p < 1)]
variable (S : Fintype)

lemma r_ineq : 0 < (r : ℝ) ∧ (r : ℝ) < 1:= sorry

lemma r_half : 1 / 2 < r := sorry

local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r

def laurent_measures.d {S}(F : ℒ S) : ℤ := (exists_bdd_filtration r_ineq.1 r_ineq.2 F).some

lemma lt_d_eq_zero (F : ℒ S) (s : S) (n : ℤ) :
  n < F.d → F s n = 0 := (exists_bdd_filtration r_ineq.1 r_ineq.2 F).some_spec s n

def θ : ℒ S → ℳ S := ϑ (1 / 2 : ℝ) r p S

def ϕ : ℒ S → ℒ S :=
begin
  rintro ⟨f,hF⟩,
  let f₁ : S → ℤ → ℤ := λ s n, 2* f s (n - 1) - f s n,
  use f₁,
  intro s,
  let g₁ : ℤ → ℝ := λ n, ∥ 2 * f s (n - 1) ∥ * r ^ n + ∥ f s n ∥ * r ^ n,
  have Hf_le_g : ∀ b : ℤ, ∥ f₁ s b ∥ * r ^ b ≤ g₁ b,
  { intro b,
    dsimp [f₁, g₁],
    rw ← add_mul,
    have rpow_pos : 0 < (r : ℝ) ^ b := by { apply zpow_pos_of_pos, rw nnreal.coe_pos,
      exact r_ineq.1, },
    apply (mul_le_mul_right rpow_pos).mpr,
    exact norm_sub_le (2 * f s (b - 1)) (f s b) },
  apply summable_of_nonneg_of_le _ Hf_le_g,
  { apply summable.add,
    have : ∀ b : ℤ, ∥ f s (b - 1) ∥ * r ^ b = r * ∥ f s (b - 1) ∥ * r ^ (b - 1),
    { intro b,
      nth_rewrite_rhs 0 mul_assoc,
      nth_rewrite_rhs 0 mul_comm,
      nth_rewrite_rhs 0 mul_assoc,
      rw [← zpow_add_one₀, sub_add_cancel b 1],
      rw [ne.def, nnreal.coe_eq_zero],
      apply ne_of_gt,
      exact r_ineq.1 },
    simp_rw [← int.norm_cast_real, int.cast_mul, normed_field.norm_mul, int.norm_cast_real,
      mul_assoc],
    apply @summable.mul_left ℝ _ _ _ _ (λ (b : ℤ), ∥f s (b - 1) ∥ * ↑r ^ b ) (∥ (2 : ℤ) ∥),
    simp_rw [this, mul_assoc],
    apply @summable.mul_left ℝ _ _ _ _ (λ (b : ℤ), ∥f s (b - 1)∥ * ↑r ^ (b - 1)) r,
    have h_comp : (λ (b : ℤ), ∥f s (b - 1)∥ * ↑r ^ (b - 1)) =
      (λ (b : ℤ), ∥f s b∥ * ↑r ^ b) ∘ (λ n, n - 1) := rfl,
    rw h_comp,
    apply summable.comp_injective _ sub_left_injective,
    repeat {apply_instance},
    repeat {specialize hF s, exact hF}, },
  { intro b,
    apply mul_nonneg,
    apply norm_nonneg,
    rw ← nnreal.coe_zpow,
    exact (r ^ b).2 },
end


-- ``[FAE]`` For this lemma, use results from ```### Sums on subtypes``` of `infinite_sum.lean`
lemma aux_summable_iff_on_nat {f : ℤ → ℤ} {ρ : ℝ≥0} (d : ℤ) (hf : ∀ n : ℤ, n < d → f n = 0) :
  summable (λ n, ∥ f n ∥ * ρ ^ n) ↔ summable (λ n : ℕ, ∥ f n ∥ * ρ ^ (n : ℤ)) := sorry
  --   suffices sum_pos : summable (λ n : ℕ, ∥ ((F.to_fun s n) : ℝ) ∥ * (1 / 2) ^ n),
  -- { let A : (set ℤ) := {n : ℤ | n + F.d ≥ 0},
  --   apply (@summable_subtype_and_compl _ _ _ _ _ _ _ A).mp,
  --   have h_supp : ∀ n : {x : ℤ // x ∉ A}, ∥ F s n ∥ * (1 / 2 : ℝ) ^ n.1 = 0, sorry,
  --   split,
  --   {sorry},
  --   { convert_to summable (λ x : {n : ℤ // n ∉ A}, ∥ F s x ∥ * (1 / 2 : ℝ) ^ (x.1)),
  --     simp_rw h_supp,
  --     apply summable_zero },
  --   repeat {apply_instance}, },
  -- sorry,

lemma summable_smaller_radius (F : ℒ S) (s : S) :
  summable (λ n, (F.to_fun s n : ℝ) * (1 / 2) ^ n) :=
begin
  -- the proof breaks with `summable (λ n, (F s n : ℝ) * (1 / 2) ^ n) :=`
 suffices abs_sum : summable (λ n, ∥ ((F.to_fun s n) : ℝ) ∥ * (1 / 2) ^ n),
  { apply summable_of_summable_norm,
    simp_rw [normed_field.norm_mul, normed_field.norm_zpow, normed_field.norm_div, real.norm_two,
      norm_one, abs_sum] },
    have pos_half : ∀ n : ℕ, 0 ≤ ∥ F s n ∥ * (1 / 2) ^ n,
    { intro n,
      apply mul_nonneg (norm_nonneg (F s n)),
      simp only [one_div, zero_le_one, inv_nonneg, zero_le_bit0, pow_nonneg] },
    have half_le_r : ∀ n : ℕ, ∥ F s n ∥ * (1 / 2) ^ n ≤ ∥ F s n ∥ * r ^ n,
    { intro n,
      apply monotone_mul_left_of_nonneg (norm_nonneg (F s n)),
      apply pow_le_pow_of_le_left,
      simp only [one_div, zero_le_one, inv_nonneg, zero_le_bit0],
      exact le_of_lt r_half },
    have h_nat_half : summable (λ n : ℕ, ∥ F.to_fun s n ∥ * (1 / 2 : ℝ≥0) ^ n) := summable_of_nonneg_of_le pos_half half_le_r ((aux_summable_iff_on_nat F.d _).mp (F.2 s)),
    apply (aux_summable_iff_on_nat F.d _).mpr h_nat_half,
    all_goals {apply lt_d_eq_zero},
end

lemma θ_ϕ_complex (F : ℒ S) : (θ S ∘ ϕ S) F = 0 :=
begin
  rcases F with ⟨f, hf⟩,
  funext,
  convert_to ∑' (n : ℤ), ((2 * f s (n - 1) - f s n) : ℝ) * (1 / 2) ^ n = 0,
  { apply tsum_congr,
    intro b,
    rw ← inv_eq_one_div,
    apply (mul_left_inj' (@zpow_ne_zero ℝ _ _ b (inv_ne_zero two_ne_zero))).mpr,
    have : (2 : ℝ) * (f s (b - 1)) = ((2 : ℤ) * (f s (b -1))) :=
      by {rw [← int.cast_one, int.cast_bit0] },
    rw [this, ← int.cast_mul, ← int.cast_sub],
    refl },
  have h_pos : has_sum (λ n, ((2 * f s (n - 1)) : ℝ) * (1 / 2) ^ n)
    (summable_smaller_radius S ⟨f, hf⟩ s).some,
  { have div_half : ∀ b : ℤ, (1 / 2 : ℝ) ^ b * (2 : ℝ) = (1 / 2) ^ ( b - 1),
    { intro b,
      rw [← inv_eq_one_div, @zpow_sub_one₀ ℝ _ _ (inv_ne_zero two_ne_zero) b],
      apply (mul_right_inj' (@zpow_ne_zero ℝ _ _ b (inv_ne_zero two_ne_zero))).mpr,
      exact (inv_inv₀ 2).symm },
    have h_comp : (λ (b : ℤ), ((f s (b - 1)) : ℝ ) * (1 / 2) ^ (b - 1)) =
      (λ (b : ℤ), ((f s b) : ℝ) * (1 / 2) ^ b) ∘ (λ n, n - 1) := rfl,
    simp_rw [mul_comm, ← mul_assoc, div_half, mul_comm, h_comp],
    let e : ℤ ≃ ℤ := ⟨λ n : ℤ, n - 1, λ n, n + 1, by {intro, simp}, by {intro, simp}⟩,
    apply (equiv.has_sum_iff e).mpr,
    exact (summable_smaller_radius S ⟨f, hf⟩ s).some_spec },
    -- sorry},--the `exact` above was ok with the old version of summable_smaller_radius
  simp_rw [sub_mul],
  rw [tsum_sub h_pos.summable, sub_eq_zero, h_pos.tsum_eq],
  exacts [(summable_smaller_radius S ⟨f, hf⟩ s).some_spec.tsum_eq.symm,
    (summable_smaller_radius S ⟨f, hf⟩ s)],
end

open finset filter
open_locale big_operators topological_space


-- **[FAE]** Use `tsum_mul_tsum_eq_tsum_sum_antidiagonal` or even better
-- `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` instead!!!
-- lemma Icc_nneg (d : ℤ) : ∀ n : ℤ, (n + d) ≥ 0 → ∀ (k ∈ finset.Icc (- d) n), n - k ≥ (0 : ℤ) := sorry

-- def g : ℕ → ℝ := λ n, ∥ (2 : ℝ) ^ (- n : ℝ) ∥

-- example (F : ℒ S) (s : S) (k : ℕ) : Prop :=
--   -- summable (λ n,
-- begin
--   have menouno := F.2 s,
--   have zero := lt_d_eq_zero S F s,
--   have uno := (aux_summable_iff_on_nat F.d zero).mp menouno,
--   have due : (r : ℝ) = ∥ (r : ℝ) ∥, sorry,
--   rw due at uno,
--   simp_rw [← normed_field.norm_zpow, ← int.norm_cast_real] at uno,
--   have h_mul : ∀ n : ℕ, ∥ ((F s n) : ℝ) ∥ * ∥ (r : ℝ) ^ (n : ℤ) ∥ = ∥ ((F s n) : ℝ) * (r ^ n) ∥ :=
--     λ n, (normed_field.norm_mul _ _).symm,
--   simp_rw h_mul at uno,
--   have quattro : summable g, sorry,
--   -- simp_rw (λ n, exact (normed_field.norm_mul _ _).symm) at uno,
--   -- simp_rw [← norm_mul] at uno,/
--   -- simp_rw [normed_field.norm_mul, normed_field.norm_zpow, normed_field.norm_div, real.norm_two,
--   --     norm_one, abs_sum] at this,

--   --simp_rw [← int.norm_cast_real, int.cast_mul, normed_field.norm_mul, int.norm_cast_real,
--       -- mul_assoc],
--   have := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm uno quattro,

--   --joke
--   use 0 = 0 ,
-- end

lemma sum_range_sum_Icc (f : ℤ → ℤ) (n d : ℤ) (hn : 0 ≤ n - d) :
 ∑ l in (range (int.eq_coe_of_zero_le hn).some.succ), (f (n - l) : ℝ) * 2 ^ l =
 ∑ k in (Icc d n), ((f k) : ℝ) * 2 ^ (n - k) :=
begin
  sorry,
end

lemma sum_Icc_sum_tail (f : ℤ → ℤ) (n d : ℤ)
  (hf : (has_sum (λ x : ℤ, (f x : ℝ) * (2 ^ x)⁻¹) 0))
  (hn : 0 ≤ n - d) : - ∑ k in (Icc d n), ((f k) : ℝ) * 2 ^ (n - k) =
  2 ^ n * tsum (λ x : {a : ℤ // a ≥ n.succ}, (f x : ℝ) * (2 ^ x.1)⁻¹) :=
begin
  sorry,
end

-- **[FAE]** Use `tsum_mul_tsum_eq_tsum_sum_antidiagonal` or even better
-- `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` instead!!!
lemma aux_summable_convolution (f : ℤ → ℤ) (hf : summable (λ n, ∥ f n ∥ * r ^ n)) : summable
  (λ n : ℤ, 2⁻¹ * ∥ tsum (λ i : ℕ, ((f (n + 1 + i)) : ℝ) * (1 / 2) ^ i) ∥ * r ^ n) :=
begin
  sorry,
  -- have one := @tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm,
  -- -- have two := summable_norm_sum_mul_range_of_summable_norm
  -- have three := _root_.has_sum_nat_add_iff',
end


-- lemma tail_little_o (f : ℤ → ℤ) (n d : ℤ) (h_sum : summable (λ n : ℤ, ∥ f n ∥ * r ^n)) :
--  tendsto (λ m, (r : ℝ) ^ m * ∥ tsum (λ x : {a : ℤ // a ≥ m + 1}, (f x : ℝ) * (1 / 2) ^ x.1) ∥ )
--   at_top (𝓝 0) :=
-- begin
--   sorry
-- end

-- for `mathlib`

open finset nat set
-- open_locale classical big_operators

-- -- def cauchy_product' (a b : ℕ → ℝ) : ℕ → ℝ :=
-- --   λ n, (∑ p : (finset.nat.antidiagonal n), (a p.1.fst) * (b p.1.snd))

-- -- lemma has_sum.cauchy_product {a b : ℕ → ℝ} {A B : ℝ} (ha : has_sum (λ n, abs a n)A) (hb : has_sum (λ n, b n) B) : has_sum (cauchy_product' a b) (A * B) :=  sorry
-- -- -- use things around has_sum_iff_tendsto_nat_of_summable_norm to derive the above from the actual cauchy_product statement

-- -- lemma summable.cauchy_product {a b : ℕ → ℝ} (ha : summable (λ n, abs a n)) (hb : summable (λ n, b n)) : summable (cauchy_product' a b) := (ha.has_sum.cauchy_product hb.has_sum).summable

-- lemma order_iso.order_bot_if {α β : Type* } [preorder α] [partial_order β]
--   [order_bot α] (f : α ≃o β) : order_bot β :=
-- begin
--   use f ⊥,
--   intro a,
--   obtain ⟨_, hx⟩ : ∃ x : α, f.1 x = a := by {apply f.1.surjective},
--   rw ← hx,
--   apply f.map_rel_iff.mpr bot_le,
-- end

-- lemma order_iso.restrict {α β : Type} [linear_order α] [preorder β] (e : α ≃o β) (s : set α) :
--   s ≃o e '' s := strict_mono_on.order_iso e.1 s (λ _ _ _ _ h, (e.strict_mono) h)

-- -- def exp_range_restrict := (real.exp_order_iso).restrict  (range (coe : ℕ → ℝ))
-- -- def ν := strict_mono.order_iso (coe : ℕ → ℝ) (@strict_mono_cast ℝ _ _)
-- def natexp := (strict_mono.order_iso (coe : ℕ → ℝ)
--   (@strict_mono_cast ℝ _ _)).trans ((real.exp_order_iso).restrict (range (coe : ℕ → ℝ)))

-- instance : order_bot ↥(⇑real.exp_order_iso '' range (coe : ℕ → ℝ)) := natexp.order_bot_if
-- instance : has_bot ↥(⇑real.exp_order_iso '' range (coe : ℕ → ℝ)) := by apply_instance

-- lemma has_bot_support (F : ℒ S) (s : S) : has_bot (function.support (F s)) :=
-- begin
--   /- The proof should just be a restatement of `laurent_measures.eq_zero_of_filtration` using the
--   above instances that guarantee that the image of n ↦ exp n has a ⊥. The second instance actually
--   must be improved, and must prove that the image of n ↦ r ^ n - c has a ⊥, for all c.
--   -/
--   sorry,
-- end

-- end `mathlib`

-- lemma kerθ_rewrite (f : ℤ → ℤ)
--   (hf : has_sum (λ n, ((f n) : ℝ) * (1 / 2) ^ n) 0) (N : ℕ) :
--   ∑ (i : ℕ) in range (N + 1), ((f i) : ℝ) * (1 / 2) ^ i = ∑'



-- example (g : ℕ → ℝ) (n : ℕ) (h : summable (λ x, g x)) : (2 : ℝ) ^ n * ∑' (x : {a // a ≥ n.succ}),
-- (g x) * (2 ^ x.val)⁻¹ =
--   2⁻¹ * ∑' (i : ℕ), g (n + 1 + i) * (2 ^ i)⁻¹ :=
-- begin
--   have one := (@tsum_smul_const ℝ ℕ ℝ _ _ _ _ _ _ g _ (2 ^ n) h).symm,
--   rw [smul_eq_mul, mul_comm] at one,
--   simp_rw [smul_eq_mul] at one,sorry,
--   -- have two

--   -- have one := λ a : ℝ, @finset.has_sum_compl_iff ℝ ℕ _ _ _ g a (range n.succ),
--   -- have two := @tsum_eq_tsum_of_has_sum_iff_has_sum ℝ ℕ _ _ _ _ _ _ one,
--   -- refine tsum_eq_tsum_of_has_sum_iff_has_sum one,
-- end

-- example (f g : ℕ → ℝ) (a b : ℝ) (h : has_sum (λ x, f x) = has_sum (λ x, g x)) :
--   ∑' (x : ℕ), f x = ∑' (x : ℕ), g x :=
-- begin
--   simp,
--   -- have hg.tsum_eq,
-- end


lemma tsum_reindex (F : ℒ S) (N : ℤ) (s : S) : ∑' (l : ℕ), (F s (N + l) : ℝ) * (2 ^ l)⁻¹ =
 2 ^ N * ∑' (m : {m : ℤ // N ≤ m}), (F s m : ℝ) * (2 ^ m.1) ⁻¹ := sorry

def ψ (F : ℒ S) (hF : θ S F = 0) : ℒ S :=
begin
  classical,
  let b : S → ℤ → ℤ := λ s n,
    if hn : n - F.d ≥ 0 then - ∑ l in range ((int.eq_coe_of_zero_le hn).some.succ),
      (F s (n -l) * (2 ^ l))
    -- if hn : n - F.d ≥ 0 then - ∑ kl in nat.antidiagonal ((int.eq_coe_of_zero_le hn).some),
    --   (2 ^ kl.snd) * (F s kl.fst)
    else 0,
  use b,
  intro s,
  -- apply (aux_summable_iff_on_nat F.d _).mpr,
  -- have h_θ : ∀ n : ℤ, ∥ b s n ∥ * r ^ (n : ℤ)  =
  --   2⁻¹ * tsum (λ i : ℕ, ((F s (n + 1 + i)) : ℝ) * (1 / 2) ^ i) * r ^ (n : ℤ), sorry,
  have h_θ : ∀ n : ℤ, ∥ b s n ∥ * r ^ (n : ℤ)  =
    2⁻¹ * ∥ tsum (λ i : ℕ, ((F s (n + 1 + i)) : ℝ) * (1 / 2) ^ i) ∥ * r ^ (n : ℤ),
  { dsimp only [b],--needed?
    intro n,
    simp only [one_div, sub_nonneg, ge_iff_le, inv_pow₀, mul_eq_mul_right_iff],
    apply or.intro_left,
    by_cases h_event : n - F.d < 0,
    { replace h_event := not_le_of_gt h_event,
      rw dif_neg h_event,
      rw tsum_reindex,
      simp only [subtype.val_eq_coe, norm_zero],
      suffices : ∑' (m : {m // n + 1 ≤ m}), (F s ↑m : ℝ) * (2 ^ ↑m)⁻¹ =
        ∑' (m : ℤ), (F s m) * (2 ^ m)⁻¹,
      { rw this,
        simp only [θ, ϑ, one_div, zpow_neg₀, inv_zpow'] at hF,
        replace hF := congr_fun hF s,
        rw real_measures.zero_apply at hF,
        simp only [zero_eq_mul, mul_eq_zero, norm_eq_zero],
        repeat {apply or.intro_right},
        apply hF, },
      { rw tsum_eq_tsum_of_has_sum_iff_has_sum,
        intro z,
        apply @has_sum_subtype_iff_of_support_subset _ _ _ _ (λ m, (F s m : ℝ) * (2 ^ m)⁻¹) z
          {m : ℤ | n + 1 ≤ m},
        rw function.support_subset_iff',
        intros a ha,
        simp only [int.cast_eq_zero, inv_eq_zero, mul_eq_zero],
        apply or.intro_left,
        simp only [not_le, mem_set_of_eq, int.lt_add_one_iff] at ha,
        apply lt_d_eq_zero,
        replace h_event := sub_neg.mp (not_le.mp h_event),
        exact lt_of_le_of_lt ha h_event,
        -- exact ha.trans h_event,
        } },
    { rw not_lt at h_event,
      let m := (int.eq_coe_of_zero_le h_event).some,
      rw dif_pos h_event,
      simp_rw [← int.norm_cast_real, int.cast_neg, int.cast_sum, int.cast_mul, int.cast_pow,
        int.cast_two],
      rw [sum_range_sum_Icc (F s) n F.d h_event, sum_Icc_sum_tail (F s) n F.d _ h_event],
      { --have pos_two := inv_nonneg.mpr (@zero_le_two ℝ _),
        -- have := abs_eq_self.mpr (inv_nonneg.mpr (@zero_le_two ℝ _)),
        rw [← (abs_eq_self.mpr (inv_nonneg.mpr (@zero_le_two ℝ _))), ← real.norm_eq_abs,
          ← normed_field.norm_mul, real.norm_eq_abs, real.norm_eq_abs, abs_eq_abs],
        apply or.intro_left,
        sorry,
      },
      { simp only [θ, ϑ, one_div] at hF,
        replace hF := congr_fun hF s,
        simp only [real_measures.zero_apply, inv_eq_one_div] at hF,
        simp_rw [← inv_zpow₀, inv_eq_one_div],
        exact (summable.has_sum_iff (summable_smaller_radius S F s)).mpr hF }}},

  apply (summable_congr h_θ).mpr,
  -- have := (summable_congr h_θ').mpr,
  -- rw [real.norm_eq_abs (r : ℝ)] at this,
  have := aux_summable_convolution (F s) (F.2 s),
  exact this,
  -- exact (summable_congr h_θ).mpr (aux_summable_convolution (F s) (F.2 s)),
end

theorem θ_ϕ_exact (F : ℒ S) (hF : θ S F = 0) : ∃ G, ϕ S G = F := sorry


-- This `θ₂` is the "measurification" of the map `θₗ` of
-- Theorem 6.9. Thus, `to_meas_θ` is the map inducing the isomorphism of Theorem 6.9 (2)
-- def θ' : laurent_measures r S → ℳ p S :=
-- λ F s, θ₀ r ⟨(λ _, F s), (λ _, F.2 s)⟩

-- lemma θ_zero :
--  (θ p r S (0 : laurent_measures r S)) = 0 := sorry

-- lemma θ_add (F G : laurent_measures r S) :
--  (θ p r S (F + G)) = (θ p r S F) + (θ p r S G) := sorry

-- This `lemma to_meas_θ_bound` is precisely Prop 7.2 (3) of `Analytic.pdf`
-- lemma θ_bound : ∃ (C : ℝ≥0), ∀ (c : ℝ≥0) (F : laurent_measures r S),
--   ∥ F ∥ ≤ c → ∥ θ p r S F ∥₊ ≤ C * c := sorry

-- def to_add_hom_θ : add_hom (laurent_measures r S) (ℳ p S) :=
-- add_monoid_hom.mk' (λ F, θ p r S F)
-- begin
--     intros a b,
--     have := θ_add p r S a b,
--     exact this,
--   end

-- def Θ : comphaus_filtered_pseudo_normed_group_hom (laurent_measures r S) (ℳ p S) :=
--   { to_fun := θ p r S,
--     bound' := θ_bound p r S,
--     continuous' := sorry, -- [FAE] I guess that this is Prop 7.2 (4) of `Analytic.pdf`
--     -- .. to_add_hom_meas_θ ξ r S p,
--     map_add' := (to_add_hom_θ p r S).2,
--     map_zero' := sorry }


-- lemma chain_complex_thm69 (F : laurent_measures r S) : Θ p r S (𝑓 • F) = 0 :=
-- begin
--   funext s,
--   sorry,
--   -- simp only [real_measures.zero_apply],
--   -- dsimp [Θ],
--   -- dsimp [to_meas_θ],
--   -- dsimp [θ],
--   -- dsimp [has_scalar],
--   -- rw pi.has_scalar,
-- end


-- From here onwards, the bundled version
-- variable [imCHFPNG : has_images (CompHausFiltPseuNormGrp.{u})]
-- variable [zerCHFPNG : has_zero_morphisms (CompHausFiltPseuNormGrp.{u})]
-- variable [kerCHFPNG : has_kernels (CompHausFiltPseuNormGrp.{u})]



-- def SES_thm69 (S : Fintype) : @category_theory.short_exact_sequence CompHausFiltPseuNormGrp.{u} _
--   imCHFPNG zerCHFPNG kerCHFPNG :=
-- { fst := bundled.of (laurent_measures r S),
--   snd := bundled.of (laurent_measures r S),
--   trd := bundled.of (ℳ p S),
--   f :=
--   begin
--     let φ := λ (F : laurent_measures r S), (ker_θ₂_generator r) • F,
--     use φ,
--     sorry,
--     sorry,
--     sorry,
--     sorry,-- [FAE] These four are the properties that the scalar multiplication by a measure on the
--     --singleton (as endomorphism of S-measures) must satisfy
--   end,
--   g := @Θ r _ S p _ _ _,
--   mono' := sorry,
--   epi' := sorry,
--   exact' := sorry }
-- end SES_thm69

end thm69
