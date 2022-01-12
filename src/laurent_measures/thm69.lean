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

open nnreal theta laurent_measures finset --filter
open_locale nnreal classical big_operators topological_space


/-**[FAE]** Use `tsum_mul_tsum_eq_tsum_sum_antidiagonal` or even better
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` instead!!!
-/

section aux_lemmas

-- for mathlib?
def range_equiv_Icc {n d : ℤ} (hn : 0 ≤ n - d) :
  range (int.eq_coe_of_zero_le hn).some.succ ≃ (Icc d n) :=
begin
  let m := (int.eq_coe_of_zero_le hn).some,
  fconstructor,
  { intro a,
    use a + d,
    simp only [mem_Icc],
    split,
    { rw le_add_iff_nonneg_left,
      exact int.of_nat_nonneg (a : ℕ) },
    { apply_rules [add_le_of_le_sub_right, (int.coe_nat_le.mpr (nat.le_of_lt_succ $
        (@mem_range m.succ a).mp _)).trans, le_of_eq],
      exacts [(Exists.some_spec (int.eq_coe_of_zero_le hn)).symm, a.2] }},
  { intro a,
    have ha := sub_nonneg.mpr ((mem_Icc).mp a.2).1,
    use (int.eq_coe_of_zero_le ha).some,
    apply mem_range_succ_iff.mpr,
    rw [← int.coe_nat_le, ← Exists.some_spec (int.eq_coe_of_zero_le ha),
      ← Exists.some_spec (int.eq_coe_of_zero_le hn), sub_le_sub_iff_right],
    exact ((mem_Icc).mp a.2).2 },
  { intro _,
    simp_rw [subtype.val_eq_coe, add_sub_cancel],
    ext,
    simp only [int.coe_nat_inj', subtype.coe_mk, coe_coe, exists_eq],
    exact ((@exists_eq' _ _).some_spec).symm },
  { intro x,
    have hx : 0 ≤ (x : ℤ) - d := sub_nonneg.mpr (mem_Icc.mp x.2).1,
    simp_rw [subtype.val_eq_coe, coe_coe, subtype.coe_mk,
      (Exists.some_spec (int.eq_coe_of_zero_le hx)).symm, sub_add_cancel],
    simp only [subtype.coe_eta] },
end

--for mathlib?
lemma sum_range_sum_Icc (f : ℤ → ℤ) (n d : ℤ) (hn : 0 ≤ n - d) :
 ∑ l in (range (int.eq_coe_of_zero_le hn).some.succ), (f (n - l) : ℝ) * 2 ^ l =
 ∑ k in (Icc d n), ((f k) : ℝ) * 2 ^ (n - k) :=
begin
  let m := (int.eq_coe_of_zero_le hn).some,
  have sum_swap : ∑ (l : ℕ) in range m.succ, (f (n - l) : ℝ) * 2 ^ l =
    ∑ (l : ℕ) in range m.succ, (f (l + d) : ℝ) * 2 ^ (m - l),
  { rw ← sub_add_cancel n d,
    rw Exists.some_spec (int.eq_coe_of_zero_le hn),
    rw [← @nat.sum_antidiagonal_eq_sum_range_succ ℝ _ (λ i j, ((f (i + d) : ℝ) * 2 ^ j)) m,
      ← nat.sum_antidiagonal_swap],
    simp only [prod.fst_swap, prod.snd_swap, zpow_coe_nat],
    simp_rw mul_comm,
    rw @nat.sum_antidiagonal_eq_sum_range_succ ℝ _ (λ i j, (2 ^ i) *
      (f (j + d) : ℝ)) m,
    simp only,
    apply sum_congr rfl,
    intros x hx,
    rw mul_eq_mul_left_iff,
    apply or.intro_left,
    have := @nat.cast_sub ℤ _ _ _ _ (mem_range_succ_iff.mp hx),
    simp only [*, int.nat_cast_eq_coe_nat, sub_left_inj, subtype.val_eq_coe] at *,
    rw [sub_eq_add_neg, add_assoc, add_comm d _, ← add_assoc, ← sub_eq_add_neg] },
  rw sum_swap,
  nth_rewrite_lhs 0 [← sum_finset_coe],
  nth_rewrite_rhs 0 [← sum_finset_coe],
  apply fintype.sum_equiv (range_equiv_Icc hn),
  intro x,
  dsimp [range_equiv_Icc],
  apply_rules [mul_eq_mul_left_iff.mpr, or.intro_left],
  rw [← sub_sub, sub_right_comm, ← zpow_coe_nat],
  apply congr_arg,
  have := @nat.cast_sub ℤ _ _ _ _ (mem_range_succ_iff.mp x.2),
  simp only [*, int.nat_cast_eq_coe_nat, sub_left_inj, subtype.val_eq_coe] at *,
  exact (Exists.some_spec (int.eq_coe_of_zero_le hn)).symm,
end

lemma sum_Icc_sum_tail (f : ℤ → ℤ) (n d : ℤ)
  (hf : (has_sum (λ x : ℤ, (f x : ℝ) * (2 ^ x)⁻¹) 0))
  (hn : 0 ≤ n - d) : - ∑ k in (Icc d n), ((f k) : ℝ) * 2 ^ (n - k) =
  2 ^ n * tsum (λ x : {a : ℤ // a ≥ n.succ}, (f x : ℝ) * (2 ^ x.1)⁻¹) :=
begin
  sorry,
end

-- **[FAE]** Use `tsum_mul_tsum_eq_tsum_sum_antidiagonal` or even better
-- `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` instead
lemma aux_summable_convolution {r : ℝ≥0} (f : ℤ → ℤ) (hf : summable (λ n, ∥ f n ∥ * r ^ n)) :
  summable (λ n : ℤ, 2⁻¹ * ∥ tsum (λ i : ℕ, ((f (n + 1 + i)) : ℝ) * (1 / 2) ^ i) ∥ * r ^ n) :=
begin
  sorry,
  -- replace hf : summable (λ n : ℕ, ∥ (f n : ℝ)* r ^ n ∥), sorry,
  -- have h_geom : summable (λ n : ℕ, ∥ (2 : ℝ) ^ n ∥), sorry,
  -- have one := @tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ℝ _ _ _ _ hf h_geom,
  -- simp_rw nat.sum_antidiagonal_eq_sum_range_succ_mk at one,
  -- have three := _root_.has_sum_nat_add_iff',
end

--for `mathlib`?
def equiv_bdd_integer_nat (N : ℤ) : ℕ ≃ {x // N ≤ x} :=
begin
  fconstructor,
  { intro n,
    use n + N,
    rw le_add_iff_nonneg_left,
    exact int.coe_nat_nonneg n },
  { rintro ⟨x, hx⟩,
    use (int.eq_coe_of_zero_le (sub_nonneg.mpr hx)).some },
  { intro a,
    simp_rw [add_tsub_cancel_right],
    exact (int.coe_nat_inj $ Exists.some_spec $ int.eq_coe_of_zero_le $ int.of_nat_nonneg a).symm },
  { rintro ⟨_, hx⟩,
    simp only,
    apply add_eq_of_eq_sub,
    exact ((int.eq_coe_of_zero_le (sub_nonneg.mpr hx)).some_spec).symm }
end

--for mathlib?
lemma int_tsum_shift (f : ℤ → ℝ) (N : ℤ) (h : summable f) :
  ∑' (x : ℕ), f (x + N) = ∑' (x : {x // N ≤ x}), f x :=
begin
  apply (equiv.refl ℝ).tsum_eq_tsum_of_has_sum_iff_has_sum rfl,
  intro _,
  apply (@equiv.has_sum_iff ℝ _ ℕ _ _ (f ∘ coe) _ ((equiv_bdd_integer_nat N))),
end

end aux_lemmas


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
        nth_rewrite_rhs 0 mul_assoc,
        nth_rewrite_rhs 0 mul_comm,
        nth_rewrite_rhs 0 mul_assoc,
        rw [← zpow_add_one₀, sub_add_cancel b 1],
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


-- ``[FAE]`` For this lemma, use results from ```### Sums on subtypes``` of `infinite_sum.lean`
lemma aux_summable_iff_on_nat {f : ℤ → ℤ} {ρ : ℝ≥0} (d : ℤ) (hf : ∀ n : ℤ, n < d → f n = 0) :
  summable (λ n, ∥ f n ∥ * ρ ^ n) ↔ summable (λ n : ℕ, ∥ f n ∥ * ρ ^ (n : ℤ)) :=
begin
  sorry,
  -- have hf : function.support (λ n : ℤ, ∥ f n ∥ * ρ ^ n) ⊆ { a : ℤ | d ≤ a},sorry,
  -- have := @has_sum_subtype_iff_of_support_subset ℝ ℤ _ _ (λ n : ℤ, ∥ f n ∥ * ρ ^ n) _ _ hf,
  -- split,
  -- { intro h,
  --   simp,

  -- },
  -- sorry,
end
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
  summable (λ n, (F s n : ℝ) * (1 / 2) ^ n) :=
begin
 suffices abs_sum : summable (λ n, ∥ ((F s n) : ℝ) ∥ * (1 / 2) ^ n),
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
    have h_nat_half : summable (λ n : ℕ, ∥ F s n ∥ * (1 / 2 : ℝ≥0) ^ n) :=
      summable_of_nonneg_of_le pos_half half_le_r ((aux_summable_iff_on_nat F.d _).mp (F.2 s)),
    apply (aux_summable_iff_on_nat F.d _).mpr h_nat_half,
    all_goals {apply lt_d_eq_zero},
end

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
  have h_pos : has_sum (λ n, ((2 * F s (n - 1)) : ℝ) * (1 / 2) ^ n)
    (summable_smaller_radius S F s).some,
  { let e : ℤ ≃ ℤ := ⟨λ n : ℤ, n - 1, λ n, n + 1, by {intro, simp}, by {intro, simp}⟩,
    convert (equiv.has_sum_iff e).mpr (summable_smaller_radius S F s).some_spec using 1,
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
  exacts [(summable_smaller_radius S F s).some_spec.tsum_eq.symm,
    (summable_smaller_radius S F s)],
end



lemma tsum_reindex (F : ℒ S) (N : ℤ) (s : S) : ∑' (l : ℕ), (F s (N + l) : ℝ) * (2 ^ l)⁻¹ =
 2 ^ N * ∑' (m : {m : ℤ // N ≤ m}), (F s m : ℝ) * (2 ^ m.1)⁻¹ :=
begin
  have h_sum := summable_smaller_radius S F s,
  simp_rw [one_div, inv_zpow'] at h_sum,
  have h_shift := int_tsum_shift (λ n, (F s n : ℝ) * (2 ^ (-n))) N h_sum,
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
    2⁻¹ * ∥ tsum (λ i : ℕ, ((F s (n + 1 + i)) : ℝ) * (1 / 2) ^ i) ∥ * r ^ (n : ℤ),
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
      rw [sum_range_sum_Icc (F s) n F.d h_event, sum_Icc_sum_tail (F s) n F.d _ h_event],
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
        exact (summable.has_sum_iff (summable_smaller_radius S F s)).mpr hF }}},
  exact (summable_congr h_θ).mpr (aux_summable_convolution (F s) (F.2 s)),
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
