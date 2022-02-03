-- import for_mathlib.short_exact_sequence
import data.int.interval
import data.finset.nat_antidiagonal
import laurent_measures.aux_lemmas
import laurent_measures.basic
import laurent_measures.theta
import linear_algebra.basic
import order.filter.at_top_bot tactic.linarith


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

open nnreal theta laurent_measures aux_thm69 finset
open_locale nnreal classical big_operators topological_space

section mem_exact

parameter {p : ℝ≥0}

def r : ℝ≥0 := (1 / 2) ^ (p:ℝ)

variables [fact(0 < p)] [fact (p < 1)]
variable (S : Fintype)

lemma r_half : 1 / 2 < r :=
begin
  calc (1/2:ℝ≥0)
      = (1/2) ^ (1:ℝ) : (rpow_one (1/2:ℝ≥0)).symm
  ... < r : rpow_lt_rpow_of_exponent_gt (half_pos zero_lt_one) (half_lt_self one_ne_zero) _,
  rw [← nnreal.coe_one, nnreal.coe_lt_coe],
  exact fact.out _
end

lemma r_pos : 0 < r := lt_of_le_of_lt zero_le' r_half

lemma r_lt_one : r < 1 :=
begin
  refine rpow_lt_one zero_le' (half_lt_self one_ne_zero) _,
  rw nnreal.coe_pos,
  exact fact.out _
end

lemma r_ineq : 0 < (r : ℝ) ∧ (r : ℝ) < 1:=
by { rw [nnreal.coe_pos, ← nnreal.coe_one, nnreal.coe_lt_coe], exact ⟨r_pos, r_lt_one⟩ }

local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r

def laurent_measures.d {S}(F : ℒ S) : ℤ := (exists_bdd_filtration r_ineq.1 r_ineq.2 F).some

lemma lt_d_eq_zero (F : ℒ S) (s : S) (n : ℤ) :
  n < F.d → F s n = 0 := (exists_bdd_filtration r_ineq.1 r_ineq.2 F).some_spec s n

def θ : ℒ S → ℳ S := ϑ (1 / 2 : ℝ) r p S

def ϕ : ℒ S → ℒ S :=
λ F,
{ to_fun := λ s n, 2 * F s (n - 1) - F s n,
  summable' := λ s, begin
    let f₁ : S → ℤ → ℤ := λ s n, 2 * F s (n - 1) - F s n,
    let g₁ : ℤ → ℝ := λ n, ∥ 2 * F s (n - 1) ∥ * r ^ n + ∥ F s n ∥ * r ^ n,
    have Hf_le_g : ∀ b : ℤ, ∥ f₁ s b ∥ * r ^ b ≤ g₁ b,
    { intro b,
      dsimp [f₁, g₁],
      rw ← add_mul,
      have rpow_pos : 0 < (r : ℝ) ^ b := by { apply zpow_pos_of_pos, rw nnreal.coe_pos,
        exact r_ineq.1, },
      apply (mul_le_mul_right rpow_pos).mpr,
      exact norm_sub_le (2 * F s (b - 1)) (F s b) },
    apply summable_of_nonneg_of_le _ Hf_le_g,
    { apply summable.add,
      have : ∀ b : ℤ, ∥ F s (b - 1) ∥ * r ^ b = r * ∥ F s (b - 1) ∥ * r ^ (b - 1),
      { intro b,
        rw [mul_assoc, mul_comm (r : ℝ), mul_assoc, ← zpow_add_one₀, sub_add_cancel b 1],
        rw [ne.def, nnreal.coe_eq_zero],
        apply ne_of_gt,
        exact r_ineq.1 },
      simp_rw [← int.norm_cast_real, int.cast_mul, normed_field.norm_mul, int.norm_cast_real,
        mul_assoc],
      apply @summable.mul_left ℝ _ _ _ _ (λ (b : ℤ), ∥F s (b - 1) ∥ * ↑r ^ b ) (∥ (2 : ℤ) ∥),
      simp_rw [this, mul_assoc],
      apply @summable.mul_left ℝ _ _ _ _ (λ (b : ℤ), ∥F s (b - 1)∥ * ↑r ^ (b - 1)) r,
      have h_comp : (λ (b : ℤ), ∥F s (b - 1)∥ * ↑r ^ (b - 1)) =
        (λ (b : ℤ), ∥F s b∥ * ↑r ^ b) ∘ (λ n, n - 1) := rfl,
      rw h_comp,
      apply summable.comp_injective _ sub_left_injective,
      repeat {apply_instance},
      repeat {exact F.summable s}, },
    { intro b,
      apply mul_nonneg,
      apply norm_nonneg,
      rw ← nnreal.coe_zpow,
      exact (r ^ b).2 },
  end }

lemma injective_ϕ (F : ℒ S) (H : ϕ S F = 0) : F = 0 := sorry

/-
open filter
open_locale filter

lemma aux_coe_nat_int_at_top : map (coe : ℕ → ℤ) at_top = at_top :=
begin
  ext s,
  simp only [set.mem_preimage, mem_at_top_sets, ge_iff_le, filter.mem_map],
  split,
  { rintros ⟨a, ha⟩,
    use a,
    intros b hb,
    lift b to ℕ,
    apply ha,
    exact_mod_cast hb,
    linarith },
  { rintro ⟨a, ha⟩,
    use a.nat_abs,
    intros b hb,
    apply ha,
    apply int.le_nat_abs.trans,
    exact_mod_cast hb }
end

lemma aux_int_filter {X : Type*} {f : ℤ → X} (F : filter X) : tendsto (λ n : ℕ, f n) at_top F ↔
  tendsto f at_top F :=
begin
  convert_to map (f ∘ coe) (at_top : filter ℕ) ≤ F ↔ tendsto f at_top F,
  simpa [← filter.map_map, aux_coe_nat_int_at_top],
end

lemma map_add_at_top_eq_int (k : ℤ) :
  map (λ a : ℤ, a + k) (at_top : filter ℤ) = (at_top : filter ℤ) :=
-- map_at_top_eq_of_gc (λa, a - k) k
--   (assume a b h, add_le_add_right h k)
--   (assume a b h, (le_tsub_iff_right h).symm)
--   (assume a h, by rw [tsub_add_cancel_of_le h])

lemma tendsto_add_top_iff_int (f : ℤ → ℝ) (d : ℤ) (a : ℝ) : tendsto (λ n : ℕ, f n) at_top (𝓝 a) ↔
  tendsto (λ n : ℕ, f (n + d)) at_top (𝓝 a) :=
begin
  rw aux_int_filter,
  convert_to tendsto f at_top (𝓝 a) ↔ tendsto (λ n, f (n + d)) at_top (𝓝 a),
  have := @aux_int_filter _ (λ n, f (n + d)) (𝓝 a),
  { simp only at this,
    rwa ← iff_eq_eq },
  { rw [iff.comm, ← tendsto_map'_iff, map_add_at_top_eq_int] },
end

-- set_option trace.simp_lemmas true
-/


-- lemma summable_smaller_radius (F : ℒ S) (s : S) :
--   summable (λ n, (F s n : ℝ) * (1 / 2) ^ n) :=
-- begin
--  suffices abs_sum : summable (λ n, ∥ ((F s n) : ℝ) ∥ * (1 / 2) ^ n),
--   { apply summable_of_summable_norm,
--     simp_rw [normed_field.norm_mul, normed_field.norm_zpow, normed_field.norm_div, real.norm_two,
--       norm_one, abs_sum] },
--     have pos_half : ∀ n : ℕ, 0 ≤ ∥ F s n ∥ * (1 / 2) ^ n,
--     { intro n,
--       apply mul_nonneg (norm_nonneg (F s n)),
--       simp only [one_div, zero_le_one, inv_nonneg, zero_le_bit0, pow_nonneg] },
--     have half_le_r : ∀ n : ℕ, ∥ F s n ∥ * (1 / 2) ^ n ≤ ∥ F s n ∥ * r ^ n,
--     { intro n,
--       apply monotone_mul_left_of_nonneg (norm_nonneg (F s n)),
--       apply pow_le_pow_of_le_left,
--       simp only [one_div, zero_le_one, inv_nonneg, zero_le_bit0],
--       exact le_of_lt r_half },
--     have h_nat_half : summable (λ n : ℕ, ∥ F s n ∥ * (1 / 2 : ℝ≥0) ^ n) :=
--       summable_of_nonneg_of_le pos_half half_le_r ((int.summable_iff_on_nat F.d _).mp (F.2 s)),
--     apply (int.summable_iff_on_nat F.d _).mpr h_nat_half,
--     all_goals {apply lt_d_eq_zero},
-- end

lemma θ_ϕ_complex (F : ℒ S) : (θ S ∘ ϕ S) F = 0 :=
begin
  funext s,
  convert_to ∑' (n : ℤ), ((2 * F s (n - 1) - F s n) : ℝ) * (1 / 2) ^ n = 0,
  { apply tsum_congr,
    intro b,
    rw ← inv_eq_one_div,
    apply (mul_left_inj' (@zpow_ne_zero ℝ _ _ b (inv_ne_zero two_ne_zero))).mpr,
    have : (2 : ℝ) * (F s (b - 1)) = ((2 : ℤ) * (F s (b - 1))),
    { rw [← int.cast_one, int.cast_bit0] },
    rw [this, ← int.cast_mul, ← int.cast_sub],
    refl },
  -- have fae := @summable_smaller_radius _ _ F.d (F.2 s) (lt_d_eq_zero _ _ _) r_half,
  have h_pos : has_sum (λ n, ((2 * F s (n - 1)) : ℝ) * (1 / 2) ^ n)
    (@summable_smaller_radius _ _ F.d (F.2 s) (lt_d_eq_zero _ _ _) r_half).some,
  { let e : ℤ ≃ ℤ := ⟨λ n : ℤ, n - 1, λ n, n + 1, by {intro, simp}, by {intro, simp}⟩,
    convert (equiv.has_sum_iff e).mpr (@summable_smaller_radius _ _ F.d (F.2 s)
      (lt_d_eq_zero _ _ _) r_half).some_spec using 1,
    ext n,
    have div_half : ∀ b : ℤ, (1 / 2 : ℝ) ^ b * (2 : ℝ) = (1 / 2) ^ (b - 1),
    { intro b,
      rw [← inv_eq_one_div, @zpow_sub_one₀ ℝ _ _ (inv_ne_zero two_ne_zero) b],
      apply (mul_right_inj' (@zpow_ne_zero ℝ _ _ b (inv_ne_zero two_ne_zero))).mpr,
      exact (inv_inv₀ 2).symm },
    rw [mul_comm, ← mul_assoc, div_half, mul_comm],
    refl, },
  simp_rw [sub_mul],
  rw [tsum_sub h_pos.summable, sub_eq_zero, h_pos.tsum_eq],
  exacts [(@summable_smaller_radius _ _ F.d (F.2 s)
    (lt_d_eq_zero _ _ _) r_half).some_spec.tsum_eq.symm,
    (@summable_smaller_radius _ _ F.d (F.2 s) (lt_d_eq_zero _ _ _) r_half)],
end


lemma tsum_reindex (F : ℒ S) (N : ℤ) (s : S) : ∑' (l : ℕ), (F s (N + l) : ℝ) * (2 ^ l)⁻¹ =
 2 ^ N * ∑' (m : {m : ℤ // N ≤ m}), (F s m : ℝ) * (2 ^ m.1)⁻¹ :=
begin
  have h_sum := @summable_smaller_radius _ _ F.d (F.2 s) (lt_d_eq_zero _ _ _) r_half,
  simp_rw [one_div, inv_zpow'] at h_sum,
  have h_shift := int_tsum_shift (λ n, (F s n : ℝ) * (2 ^ (-n))) N,
  simp only at h_shift,
  simp_rw [subtype.val_eq_coe, ← zpow_neg₀],
  rw [← h_shift, ← _root_.tsum_mul_left, tsum_congr],
  intro n,
  nth_rewrite_rhs 0 [mul_comm],
  rw [mul_assoc, ← (zpow_add₀ (@two_ne_zero ℝ _ _)), neg_add_rev, neg_add_cancel_comm, zpow_neg₀,
    zpow_coe_nat, add_comm],
end

def ψ (F : ℒ S) (hF : θ S F = 0) : ℒ S :=
begin
  let b : S → ℤ → ℤ := λ s n,
    if hn : n - F.d ≥ 0 then - ∑ l in range ((int.eq_coe_of_zero_le hn).some.succ),
      (F s (n -l) * (2 ^ l))
    else 0,
  use b,
  intro s,
  have h_θ : ∀ n : ℤ, ∥ b s n ∥ * r ^ (n : ℤ)  =
    (1 / 2) * ∥ tsum (λ i : ℕ, ((F s (n + 1 + i)) : ℝ) * (1 / 2) ^ i) ∥ * r ^ (n : ℤ),
  { dsimp only [b],
    intro n,
    simp only [one_div, sub_nonneg, ge_iff_le, inv_pow₀, mul_eq_mul_right_iff],
    apply or.intro_left,
    by_cases h_event : n - F.d < 0,
    { replace h_event := not_le_of_gt h_event,
      rw sub_nonneg at h_event,
      rw [dif_neg h_event, tsum_reindex],
      simp only [subtype.val_eq_coe, norm_zero],
      suffices : ∑' (m : {m // n + 1 ≤ m}), (F s ↑m : ℝ) * (2 ^ (- ↑m)) =
        ∑' (m : ℤ), (F s m) * (2 ^ (-m)),
      { simp_rw [← zpow_neg₀],
        rw this,
        simp only [θ, ϑ, one_div, inv_zpow'] at hF,
        replace hF := congr_fun hF s,
        rw real_measures.zero_apply at hF,
        simp only [zero_eq_mul, mul_eq_zero, norm_eq_zero],
        repeat {apply or.intro_right},
        apply hF, },
      { rw tsum_eq_tsum_of_has_sum_iff_has_sum,
        intro z,
        apply @has_sum_subtype_iff_of_support_subset _ _ _ _ (λ m, (F s m : ℝ) * (2 ^ (- m))) z
          {m : ℤ | n + 1 ≤ m},
        rw function.support_subset_iff',
        intros a ha,
        simp only [int.cast_eq_zero, inv_eq_zero, mul_eq_zero],
        apply or.intro_left,
        simp only [not_le, set.mem_set_of_eq, int.lt_add_one_iff] at ha,
        apply lt_d_eq_zero,
        rw ← sub_nonneg at h_event,
        replace h_event := sub_neg.mp (not_le.mp h_event),
        exact lt_of_le_of_lt ha h_event,
        } },
    { rw not_lt at h_event,
      let m := (int.eq_coe_of_zero_le h_event).some,
      rw sub_nonneg at h_event,
      rw dif_pos h_event,
      simp_rw [← int.norm_cast_real, int.cast_neg, int.cast_sum, int.cast_mul, int.cast_pow,
        int.cast_two],
      rw ← sub_nonneg at h_event,
      rw [sum_range_sum_Icc (coe ∘ (F s)) n F.d h_event,
        sum_Icc_sum_tail (F s) n F.d _ (lt_d_eq_zero S F s) h_event],
      { rw [← (abs_eq_self.mpr (inv_nonneg.mpr (@zero_le_two ℝ _))), ← real.norm_eq_abs,
          ← normed_field.norm_mul, real.norm_eq_abs, real.norm_eq_abs, abs_eq_abs,
          ← (sub_add_cancel n 1), (sub_eq_add_neg n 1), (add_assoc n _), (add_comm n _),
          (add_assoc (-1 : ℤ) _ _), (add_comm 1 n), zpow_add₀ (@two_ne_zero ℝ _ _),
          ← (add_assoc (-1 : ℤ) _ _), neg_add_cancel_comm, ← int.succ, mul_assoc, zpow_neg₀,
          zpow_one],
        apply or.intro_left,
        rw ← tsum_reindex S F n.succ s },
      { simp only [θ, ϑ, one_div] at hF,
        replace hF := congr_fun hF s,
        simp only [real_measures.zero_apply, inv_eq_one_div] at hF,
        simp_rw [← inv_zpow₀, inv_eq_one_div],
        exact (summable.has_sum_iff (@summable_smaller_radius _ _ F.d (F.2 s) (lt_d_eq_zero _ _ _)
          r_half)).mpr hF }}},
  have : ∀ (n : ℤ), n < F.d → ∥∑' (i : ℕ), (F s (n + 1 + i) : ℝ) * (1 / 2) ^ i∥ = 0,
  { intros n hn,
    replace hn := not_le_of_gt (sub_neg.mpr hn),
    specialize h_θ n,
    simp only [mul_eq_mul_right_iff, zpow_ne_zero n (nnreal.coe_ne_zero.mpr (ne_of_lt r_pos).symm),
      or_false] at h_θ,
    convert_to 1 / 2 * ∥∑' (i : ℕ), (F s (n + 1 + i) : ℝ) * (1 / 2) ^ i∥ = 0 using 0,
    simp only [one_div, mul_eq_zero, inv_eq_zero, bit0_eq_zero, one_ne_zero, false_or],
    rw [← h_θ, norm_eq_zero],
    dsimp [b],
    rw dif_neg hn },
  refine (summable_congr h_θ).mpr
    (aux_thm69.summable_convolution r_pos r_half (F s) F.d (F.2 s) (lt_d_eq_zero S F s)
    this),
end

theorem θ_ϕ_exact (F : ℒ S) (hF : θ S F = 0) : ∃ G, ϕ S G = F :=
begin
  use ψ S F hF,
  ext s n,
  dsimp [ϕ, ψ],
  simp,
  by_cases hn : F.d ≤ n - 1,
  { --have hx' := hx.trans (sub_le_self x zero_le_one),
    rw [dif_pos hn, dif_pos $ hn.trans $ sub_le_self n zero_le_one, neg_eq_neg_one_mul, ← mul_assoc,
      mul_comm (2 : ℤ) (-1 : ℤ), mul_assoc, mul_sum, ← neg_eq_neg_one_mul,
      neg_sub_neg, finset.sum_range_succ', sub_eq_iff_eq_add'],
    simp only [pow_zero, sub_zero, mul_one, int.coe_nat_zero, int.coe_nat_add, int.coe_nat_one,
      add_comm _ (1:ℤ), ← sub_sub n 1],
    congr' 1,
    refine finset.sum_congr _ _,
    { congr' 1,
      apply int.coe_nat_inj,
      rw ← sub_nonneg at hn,
      have := (int.eq_coe_of_zero_le hn).some_spec,
      simp only [int.coe_nat_succ, ← sub_eq_iff_eq_add],
      convert this using 1,
      transitivity n - F.d - 1,
      { congr' 1,
        have : 0 ≤ n - F.d, { linarith },
        symmetry, exact (int.eq_coe_of_zero_le this).some_spec },
      { ring_nf } },
    { intros i hi, rw pow_succ, ring_nf, }, },
  { rw [dif_neg hn, mul_zero, zero_sub],
    by_cases hn' : F.d ≤ n,
    { rw [dif_pos hn', neg_neg],
      have hn'' : F.d = n,
      -- rw not_le at hn,
      apply eq_of_le_of_not_lt hn',
      rw not_lt,
      exact int.le_of_sub_one_lt (not_le.mp hn),
      -- rw neg_neg,
      sorry,

    },
    { rw dif_neg hn',
      exact (lt_d_eq_zero S F s n (not_le.mp hn')).symm }}
end

end mem_exact

-- def Θ : comphaus_filtered_pseudo_normed_group_hom (laurent_measures r S) (ℳ p S) :=
--   { to_fun := θ p r S,
--     bound' := θ_bound p r S,
--     continuous' := , -- [FAE] I guess that this is Prop 7.2 (4) of `Analytic.pdf`
--     -- .. to_add_hom_meas_θ ξ r S p,
--     map_add' := (to_add_hom_θ p r S).2,
--     map_zero' :=  }


-- lemma chain_complex_thm69 (F : laurent_measures r S) : Θ p r S (𝑓 • F) = 0 :=
-- begin
--   funext s,
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
--     use φ,-- [FAE] These four are the properties that the scalar multiplication by a measure on the
--     --singleton (as endomorphism of S-measures) must satisfy
--   end,
--   g := @Θ r _ S p _ _ _,
--   mono' :=
--   epi' :=
--   exact' := }
-- end SES_thm69
