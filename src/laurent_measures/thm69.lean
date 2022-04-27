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
  for `r = 2^(1/p)` by `T⁻¹-2`.
* `ψ` corresponds to dividing a Laurent series by `(T⁻¹-2)`. It is defined only on series
  vanishing at `1/2`, so that it again takes values in `ℒ S`
* The maps `Θ`, `Φ` and `Ψ` are the "measurifications" of `θ`, `ϕ` and `ψ`,
  so they are morphisms in the right category (**[FAE]** Not here any more!)

The main results are
* `injective_ϕ` stating that `ϕ` is injective;
* `θ_ϕ_complex` stating that `ϕ ∘ θ = 0`; and
* `θ_ϕ_exact` stating that the kernel of `θ` coincides with the image of `ϕ`.
Together with `ϑ_surjective` from `laurent_measures.theta` (specialized at `ξ=1/2`, so that `ϑ` is
`θ`) this is the statement of Theorem 6.9 of `Analytic.pdf` of interest to us, although only "on
elements" and not yet as a Short Exact Sequence in the right category.
-/

noncomputable theory

open nnreal theta laurent_measures aux_thm69 finset
open_locale nnreal classical big_operators topological_space

section phi

parameter {r : ℝ≥0}

local notation `ℒ` := laurent_measures r
variables [fact (0 < r)]
variable {S : Fintype}

def ϕ : ℒ S → ℒ S :=
λ F, shift (1) F - 2 • F

lemma ϕ_apply (F : ℒ S) (s : S) (n : ℤ) : ϕ F s n = F s (n+1) - 2 * F s n :=
by simp only [ϕ, sub_apply, nsmul_apply, shift_to_fun_to_fun, nsmul_eq_mul]; refl

lemma ϕ_natural (S T : Fintype) (f : S ⟶ T) : --[fact (0 < p)] [fact ( p ≤ 1)] :
  ϕ ∘ laurent_measures.map_hom f = laurent_measures.map_hom f ∘ ϕ :=
begin
  ext F t n,
  simp only [ϕ, sum_sub_distrib, mul_sum, function.comp_app, map_hom_to_fun, sub_apply,
    nsmul_apply, shift_to_fun_to_fun,
    map_apply, nsmul_eq_mul, mul_ite, mul_zero], -- squeezed for time
end

-- #check @ϕ

lemma tsum_reindex (F : ℒ S) (N : ℤ) (s : S) : ∑' (l : ℕ), (F s (N + l) : ℝ) * (2 ^ l)⁻¹ =
 2 ^ N * ∑' (m : {m : ℤ // N ≤ m}), (F s m : ℝ) * (2 ^ m.1)⁻¹ :=
begin
  have h_shift := int_tsum_shift (λ n, (F s n : ℝ) * (2 ^ (-n))) N,
  simp only at h_shift,
  simp_rw [subtype.val_eq_coe, ← zpow_neg₀],
  rw [← h_shift, ← _root_.tsum_mul_left, tsum_congr],
  intro n,
  rw [mul_comm (_ ^ N), mul_assoc, ← (zpow_add₀ (@two_ne_zero ℝ _ _)), neg_add_rev,
    neg_add_cancel_comm, zpow_neg₀, zpow_coe_nat, add_comm],
end

variable [fact (r < 1)]

lemma injective_ϕ (F : ℒ S) (H : ϕ F = 0) : F = 0 :=
begin
  dsimp only [ϕ] at H, rw [sub_eq_zero] at H,
  replace H : ∀ n : ℤ, ∀ s : S, 2 * F s (n - 1) = F s n,
  { intros n s,
    rw laurent_measures.ext_iff at H,
    convert (H s (n-1)).symm using 1,
    { rw [two_smul, two_mul], refl, },
    { simp [shift] } },
  ext s n,
  apply int.induction_on' n (F.d - 1),
  { refine lt_d_eq_zero _ _ (F.d - 1) _,
    simp only [sub_lt_self_iff, zero_lt_one], },
  { intros k h hk₀,
    simp [← H (k + 1) s, add_sub_cancel, hk₀, mul_zero] },
  { intros k h hk₀,
    simpa only [hk₀, mul_eq_zero, bit0_eq_zero, one_ne_zero, false_or, zero_apply] using H k s }
end

end phi

section mem_exact

parameter {p : ℝ≥0}

def r : ℝ≥0 := (1 / 2) ^ (p:ℝ)

lemma r_pos : 0 < r :=
suffices 0 < (2 : ℝ≥0)⁻¹ ^ (p : ℝ), by simpa [r],
rpow_pos (nnreal.inv_pos.mpr zero_lt_two)

instance r_pos' : fact (0 < r) := ⟨r_pos⟩

lemma r_coe : (1 / 2 : ℝ) ^ (p : ℝ) = (r : ℝ) :=
begin
  have : (1/2 : ℝ) = ((1/2 : ℝ≥0) : ℝ),
  simp only [one_div, nonneg.coe_inv, nnreal.coe_bit0, nonneg.coe_one],
  rw [this, ← nnreal.coe_rpow, nnreal.coe_eq],
  refl,
end

variable [fact(0 < p)]

lemma r_lt_one : r < 1 :=
begin
  refine rpow_lt_one (half_lt_self one_ne_zero) _,
  rw nnreal.coe_pos,
  exact fact.out _
end

instance r_lt_one' : fact (r < 1) := ⟨r_lt_one⟩

variable {S : Fintype}

local notation `ℒ` := laurent_measures r
local notation `ℳ` := real_measures p

theorem nnreal.rpow_int_cast (x : nnreal) (n : ℤ) : x ^ (n : ℝ) = x ^ n :=
begin
  apply subtype.ext,
  simp,
end

def θ : ℒ S → ℳ S := ϑ (1 / 2 : ℝ) r p S

lemma θ_natural [fact (0 < p)] [fact (p ≤ 1)] (S T : Fintype) (f : S ⟶ T) (F : ℒ S) (t : T) :
  θ (map f F) t = real_measures.map f (θ F) t :=
begin
  simp only [θ, ϑ, one_div, map_apply, int.cast_sum, inv_zpow', zpow_neg₀, real_measures.map_apply],
  rw ← tsum_sum,
  { congr', ext n, exact sum_mul, },
  intros,
  rw mem_filter at H,
  rcases H with ⟨-, rfl⟩,
  have := F.summable i,

  refine summable.add_compl (_ : summable (_ ∘ (coe : {n : ℤ | 0 ≤ n} → ℤ))) _,
  {
    have moo := summable.comp_injective this
      (subtype.coe_injective : function.injective (coe : {n : ℤ | 0 ≤ n} → ℤ)),
    refine summable_of_norm_bounded _ (moo) _, clear moo this,
--    have foo := summable.summable_of_eq_zero_or_self this,
    rintro ⟨n, (hn : 0 ≤ n)⟩,
    simp only [function.comp_app, subtype.coe_mk, norm_mul, norm_inv, norm_zpow, real.norm_two],
    rw (F i n).norm_cast_real,
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
    delta r,
    delta r,
    rw (by push_cast : ((2 : ℝ) ^ n)⁻¹ = ((2 ^ n)⁻¹ : nnreal)),
    norm_cast,
    rw [← nnreal.rpow_int_cast, ← inv_rpow],
    rw nnreal.rpow_int_cast,
    set m := n.nat_abs with hm,
    have hmn : n = m := by { rw hm, exact int.eq_nat_abs_of_zero_le hn },
    rw hmn,
    norm_cast,
    apply pow_le_pow_of_le, clear hn hmn hm m n,
    rw (show (2 : nnreal)⁻¹ = (1 / 2) ^ (1 : ℝ), by simp;norm_num),
    refine rpow_le_rpow_of_exponent_ge _ _ _,
    { simp },
    { simp, norm_num },
    { exact_mod_cast (fact.elim infer_instance),
      apply_instance, } },
  {
    obtain ⟨d, hd⟩ := exists_bdd_filtration (r_pos) (r_lt_one) F,
    apply summable_of_ne_finset_zero, -- missing finset
    swap, exact (finset.subtype _ (finset.Ico d 0)),
    rintros ⟨z, (hz : ¬ (0 ≤ z))⟩ hz2,
    simp only [subtype.coe_mk, mul_eq_zero, int.cast_eq_zero, inv_eq_zero],
    left,
    apply hd,
    simp only [mem_subtype, subtype.coe_mk, mem_Ico, not_and, not_le] at hz2,
    by_contra h,
    push_neg at h,
    apply hz,
    specialize hz2 h,
    push_neg at hz2,
    exact hz2 },
end

variables [fact (p < 1)]

lemma r_half : 1 / 2 < r :=
calc (1/2:ℝ≥0)
    = (1/2) ^ (1:ℝ) : (rpow_one (1/2:ℝ≥0)).symm
... < r : rpow_lt_rpow_of_exponent_gt (half_pos zero_lt_one) (half_lt_self one_ne_zero) $
(nnreal.coe_lt_coe.mpr (fact.out _)).trans_le (nnreal.coe_one).le

lemma laurent_measures.summable_half (F : ℒ S) (s : S) :
  summable (λ n, ((F s n) : ℝ) * (1 / 2) ^ n) :=
aux_thm69.summable_smaller_radius F.d (F.summable s) (λ n hn, lt_d_eq_zero _ _ _ hn) r_half

lemma θ_ϕ_complex (F : ℒ S) : (θ ∘ ϕ) F = 0 :=
begin
  have t0 : (2 : ℝ)⁻¹ ≠ 0 := inv_ne_zero two_ne_zero,
  funext s,
  convert_to ∑' (n : ℤ), ((F s (n + 1) - 2 * F s n) : ℝ) * (1 / 2) ^ n = 0,
  { apply tsum_congr,
    intro b,
    field_simp [ϕ] },
  simp_rw [sub_mul],
  rw [tsum_sub, sub_eq_zero],
  -- old proof was slicker :-(
  { refine tsum_eq_tsum_of_ne_zero_bij (λ i, (i.val : ℤ) - 1) _ _ _,
    { rintros ⟨x, _⟩ ⟨y, _⟩ h, dsimp at *, linarith },
    { rintros x hx,
      refine ⟨⟨x + 1, _⟩, _⟩,
      { rw function.mem_support at ⊢ hx,
        convert hx using 1,
        simp [zpow_add₀],
        ring },
      { simp } },
    { rintro ⟨i, hi⟩,
      simp [zpow_sub₀],
      ring } },
  { rw ← (equiv.add_group_add (-1 : ℤ)).summable_iff,
    simp only [function.comp, one_div, inv_zpow', equiv.add_group_add_apply,
      neg_add_cancel_comm],
    convert summable.mul_right 2 (F.summable_half s),
    ext x,
    simp [zpow_add₀], ring },
  { simp_rw [mul_assoc],
    convert (F.summable_half s).mul_left 2 },
end
.

lemma int.nat_bdd_of_summable (a : ℤ → ℝ) (ha : summable a) (m : ℤ) :
  ∥∑' (n : ℕ), a (m + n)∥ ≤ ∑' (z : ℤ), ∥a z∥ :=
begin
  have hinj : function.injective (λ (n : ℕ), m + n),
  { rintros a b (h : m + a = m + b),
    simpa using h },
  rw ← summable_norm_iff at ha,
  refine le_trans (norm_tsum_le_tsum_norm (ha.comp_injective hinj)) _,
  exact tsum_le_tsum_of_inj _ hinj (λ _ _, norm_nonneg _) (λ _, le_refl _)
    (ha.comp_injective hinj) ha,
end

lemma psi_def_aux2 (a : ℤ → ℝ) (ha : summable a) (s : ℝ) (hs1 : 0 ≤ s) (hs2 : s < 1) (d : ℤ) :
  summable (λ (k : ℕ), (∑' (n : ℕ), ∥a (d + k + n)∥) * s^k) :=
begin
  rw ← summable_norm_iff,
  simp_rw [norm_mul, norm_pow],
  refine summable_of_nonneg_of_le _ _ (_ : summable (λ (k : ℕ), (∑' (z : ℤ), ∥a z∥) * ∥s∥^k)),
  { intros,
    exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _) },
  { intros,
    apply mul_le_mul_of_nonneg_right,
    { rw real.norm_of_nonneg,
      { have hinj : function.injective (λ (n : ℕ), d + b + n),
        { rintros x y (h : d + b + x = d + b + y),
          simpa using h },
        rw ← summable_norm_iff at ha,
        refine tsum_le_tsum_of_inj _ hinj (λ _ _, norm_nonneg _) (λ _, le_refl _) _ ha,
        exact ha.comp_injective hinj },
      { refine tsum_nonneg (λ _, (norm_nonneg _)) } },
    { exact (pow_nonneg (norm_nonneg _) _) } },
  { apply summable.mul_left,
    rw summable_geometric_iff_norm_lt_1,
    rw [norm_norm, real.norm_eq_abs, abs_lt],
    split; linarith },
end

-- probably true; Zulip says this is the wrong lemma
-- lemma summable_snd_of_summable_fst {α : Type*} (F : α → α → ℝ) (h_nonneg : ∀ n k, 0 ≤ F n k)
--   (h_rows : ∀ n, summable (λ k, F n k)) (h_cols : ∀ k, summable (λ n, F n k))
--   (h_col_row : summable (λ k, ∑' n, F n k)) : summable (λ n, ∑' k, F n k) :=
-- begin
--   sorry
-- end

-- probably false -- `this` terms are not nonnegative so switching order of
-- summation won't work. `this` needs to have absolute values
-- lemma psi_def_aux3 {S : Fintype} [fact (0 < p)] [fact (p < 1)] (F : ℒ S) (s : ↥S)
--   (this : summable (λ (k : ℕ),
--     (∑' (n : ℕ), (F s (F.d + ↑k + ↑n) : ℝ) * ↑r ^ (F.d + ↑k + ↑n)) *
--       (1 / (2 * ↑r)) ^ k)) :
--   summable (λ (n : ℕ), (-(2 : ℝ) ^ (F.d + ↑n - 1) *
--     ∑' (k : ℕ), ↑(F s (F.d + ↑n + ↑k)) * (1 / 2) ^ (F.d + ↑n + ↑k)) * ↑r ^ (F.d + ↑n)) :=
-- begin
--   -- get out power of 1/2
--   conv begin
--     congr,
--     funext,
--     rw [zpow_sub₀ (show (2 : ℝ) ≠ 0, from two_ne_zero),
--       zpow_one, div_eq_mul_inv, mul_comm _ (2 : ℝ)⁻¹, ← neg_mul, mul_assoc,
--       mul_assoc, ← _root_.tsum_mul_right, ← _root_.tsum_mul_left],
--   end,
--   apply summable.mul_left,
--   rw ← summable_norm_iff,
--   sorry,
--   -- rw summable_sup
--   -- summable_mul_of_summable_norm
-- end

-- probably should rewrite because of norm error earlier
-- lemma psi_def_aux {S : Fintype} [fact (0 < p)] [fact (p < 1)] (F : ℒ S) (s : ↥S)
--   (F_sum : summable (λ (n : ℤ), ∥F s n∥ * ↑r ^ n)) :
--   summable (λ (n : ℤ), ∥ite (F.d ≤ n) (-(2 : ℝ) ^ (n - 1) *
--     ∑' (k : ℕ), ↑(F s (n + ↑k)) * (1 / 2) ^ (n + ↑k)) 0∥ * ↑r ^ n) :=
-- begin
--   suffices : summable (λ (n : ℤ), (ite (F.d ≤ n) (-(2 : ℝ) ^ (n - 1) *
--     ∑' (k : ℕ), ↑(F s (n + ↑k)) * (1 / 2) ^ (n + ↑k)) 0) * ↑r ^ n),
--   { rw ← summable_norm_iff at this,
--     simp_rw norm_mul at this,
--     convert this,
--     ext,
--     congr',
--     rw real.norm_of_nonneg,
--     apply zpow_nonneg,
--     apply r_pos.le },
--   -- t = n - d, n = d + t
--   suffices : summable (λ n : ℕ, (-(2 : ℝ) ^ (F.d + n - 1) *
--     ∑' (k : ℕ), ↑(F s (F.d + n + ↑k)) * (1 / 2) ^ (F.d + n + ↑k)) * ↑r ^ (F.d + n)),
--   { have hinj : function.injective (λ (n : ℕ), F.d + n),
--     { rintros a b (h : F.d + a = F.d + b),
--       simpa using h },
--       rw ← function.injective.summable_iff hinj, swap,
--       { intros x hx,
--         rw if_neg, simp,
--         intro hdx,
--         apply hx,
--         use (x - F.d).nat_abs,
--         dsimp only,
--         rw int.nat_abs_of_nonneg, ring,
--         linarith },
--       { convert this,
--         ext n,
--         simp } },
-- --  have half := F.summable_half s,
--   have hsum : summable (λ n, (F s n : ℝ) * r ^ n),
--   { rw ← summable_norm_iff,
--     simp_rw norm_mul,
--     convert F_sum, ext n,
--     norm_cast, simp },
--   have := psi_def_aux2 (λ n, F s n * r^n) hsum (1/(2*r)) _ _ F.d,
--   { dsimp at this,
--     apply psi_def_aux3,
--     sorry, }, -- exact this GAARGH
--   { refine div_nonneg zero_le_one (mul_nonneg zero_le_two (zero_le_coe)) },
--   { simp only [one_div, norm_inv, norm_mul, real.norm_two, norm_eq],
--     rw _root_.inv_lt_one_iff, right,
--     have := r_half,
--     have : (1 : ℝ) / 2 < r, assumption_mod_cast,
--     linarith },
-- end

def ψ (F : ℒ S) (hF : θ F = 0) : ℒ S :=
{ to_fun := λ s n, if F.d ≤ n then
    ∑ l in range (n - F.d).nat_abs.succ, F s (n - 1 - l) * (2 ^ l)
    else 0,
  summable' := λ s, begin
    -- make everything real
    change summable (λ (n : ℤ),
     ∥((ite (F.d ≤ n)
       (∑ (l : ℕ) in range (n - F.d).nat_abs.succ, F s (n - 1 - ↑l) * 2 ^ l) 0 : ℤ) : ℝ)∥₊
     * r ^ n),
    push_cast,
    -- hypothesis that infinite sum converges at r>1/2
    have := F.summable s,
    -- get hypothesis that infinite sum is 0 at 1/2
    simp only [θ, ϑ] at hF,
    replace hF := congr_fun hF s, dsimp at hF,
    -- change sum from ℤ to ℕ
    --rw nnreal.summable_iff_on_nat_less F.d, swap,
    --{ intros n hn, simp [if_neg hn.not_le] },
    have h1 : ∀ (n : ℤ),
      ite (F.d ≤ n) (∑ (l : ℕ) in range (n - F.d).nat_abs.succ, (F s (n - 1 - ↑l) : ℝ) * 2 ^ l) 0 =
      ite (F.d ≤ n) (-(2 : ℝ)^(n-1)*∑' (k : ℕ), F s (n + k) * (1/2) ^ (n + k)) 0,
    { intro n,
      split_ifs with hn, swap, refl,
      rw [← inv_mul_eq_iff_eq_mul₀, ← neg_inv, neg_mul, mul_sum, neg_eq_iff_add_eq_zero, ← hF],
        swap, exact neg_ne_zero.2 (zpow_ne_zero _ two_ne_zero),
      convert @tsum_add_tsum_compl ℝ ℤ _ _ _ _ _ {x : ℤ | x < n}
        (summable.subtype (F.summable_half s) _) (summable.subtype (F.summable_half s) _) using 2,
      { simp_rw [← inv_zpow₀, inv_eq_one_div, mul_comm (((1 : ℝ)/2)^(n-1)), mul_assoc],
        simp_rw (show ∀ (x : ℕ), (2 : ℝ)^x = (1/2)^(-(x : ℤ)), by {intros, simp}),
        simp_rw [← zpow_add₀ (by norm_num : (1 : ℝ) / 2 ≠ 0), add_comm, ← sub_eq_add_neg],
        rw ← tsum_eq_sum,
        convert @equiv.tsum_eq ℝ _ _ _ _ _
          (⟨λ m, ⟨n - 1 - m, lt_of_le_of_lt (sub_le_self _ (int.coe_zero_le m)) (sub_one_lt n)⟩,
           (λ z, (n - 1 - z.1).nat_abs), λ m, by simp, λ ⟨z, hz⟩, subtype.ext begin
--             squeeze_simp,
             change n - 1 - (n - 1 - z).nat_abs = z,
             rw ← int.eq_nat_abs_of_zero_le (sub_nonneg_of_le (int.le_sub_one_of_lt hz)),
             ring, end⟩ : ℕ ≃ {z : ℤ // z < n}) _,
        { ext, refl },
        { intros b hb,
          rw mul_eq_zero, left,
          norm_cast,
          apply lt_d_eq_zero,
          by_contra h, push_neg at h, apply hb,
          rw [mem_range, nat.succ_eq_add_one, ← int.coe_nat_lt, int.coe_nat_add,
            ← int.eq_nat_abs_of_zero_le]; linarith } },
      { convert @equiv.tsum_eq ℝ _ _ _ _ _
          (⟨λ x, ⟨n + x, (int.le.intro rfl).not_lt⟩, (λ z, (z.1 - n).nat_abs),
            λ x, by simp, λ ⟨x, hx⟩, subtype.ext begin
              change n + _ = x,
              rw ← int.eq_nat_abs_of_zero_le (sub_nonneg.2 (le_of_not_lt hx)),
              exact add_eq_of_eq_sub' rfl,
            end⟩ : ℕ ≃ {z : ℤ // ¬ z < n}) _,
        ext, refl },
    },
    suffices : summable (λ (n : ℤ),
     ∥ite (F.d ≤ n) (-(2 : ℝ)^(n-1)*∑' (k : ℕ), ↑(F s (n + k)) * (1/2) ^ (n + k)) 0∥₊ *
       r ^ n),
    { refine (summable_congr _).2 this,
      intro n,
      congr' 2,
      apply h1 n,
    }, clear h1,
    -- next line goes from ℝ≥0 to ℝ
    simp only [←nnreal.summable_coe, nonneg.coe_mul, _root_.coe_nnnorm, nnreal.coe_zpow, summable_congr],
    exact psi_def_aux F s this,
  end }

theorem θ_ϕ_exact (F : ℒ S) (hF : θ F = 0) : ∃ G, ϕ G = F :=
begin
  use ψ F hF,
  ext s n,
  simp only [ϕ, ψ, sub_apply, shift_to_fun_to_fun, laurent_measures.coe_mk, nsmul_apply,
    nsmul_eq_mul, int.nat_cast_eq_coe_nat, int.coe_nat_succ, int.coe_nat_zero, zero_add],
  split_ifs with h1 h2,
  { rw [sum_range_succ', (by norm_num : (1 : ℤ) + 1 = 2), mul_sum],
    convert add_sub_cancel' _ _,
    { rw [nat.succ_eq_add_one, (by ring : n + 1 - F.d = n - F.d + 1)],
      obtain ⟨m, hm⟩ := (int.eq_coe_of_zero_le (sub_nonneg.mpr h2)),
      rw hm,
      norm_cast },
    { ext,
      push_cast,
      ring_exp,
      congr' 2,
      ring },
    { simp } },
  { have hF : F.d = n + 1, linarith,
    simp [hF] },
  { linarith },
  { exact (lt_d_eq_zero F s n (not_le.mp h)).symm },
end

end mem_exact
