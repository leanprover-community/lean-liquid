import topology.algebra.infinite_sum
import topology.instances.ennreal

open_locale ennreal

open_locale nnreal

-- don't need it but maybe useful?
lemma ennreal.summable_of_coe_sum_eq {X : Type*} (f g : X → ℝ≥0)
  (h : ∑' x, (f x : ℝ≥0∞) = ∑' x, (g x : ℝ≥0∞)) :
  summable f ↔ summable g :=
by rw [← ennreal.tsum_coe_ne_top_iff_summable, h, ennreal.tsum_coe_ne_top_iff_summable]

lemma ennreal.has_sum_comm {α β: Type*} (F : α → β → ℝ≥0∞) (s : ℝ≥0∞)
  : has_sum (λ n, ∑' k, F n k) s ↔ has_sum (λ k, ∑' n, F n k) s :=
by rw [ summable.has_sum_iff ennreal.summable, summable.has_sum_iff ennreal.summable,
    ennreal.tsum_comm ]

-- do we need the `real` version?
-- /-- sum of row sums equals sum of column sums -/
-- lemma real.summable_snd_of_summable_fst {α β: Type*} (F : α → β → ℝ) (h_nonneg : ∀ n k, 0 ≤ F n k)
--   (h_rows : ∀ n, summable (λ k, F n k)) (h_cols : ∀ k, summable (λ n, F n k))
--   (h_col_row : summable (λ k, ∑' n, F n k)) : summable (λ n, ∑' k, F n k) :=
-- begin

--   -- wrong idea have := summable (λ ab : α × β, F ab.1 ab.2),
--   admit,
-- end

lemma ennreal.mul_le_mul_of_right {a b c : ℝ≥0∞} (hab : a ≤ b) : a * c ≤ b * c :=
begin
  rcases eq_or_ne c 0 with (rfl | hc0),
  { simp },
  { rcases eq_or_ne c ⊤ with (rfl | hctop),
    { rw [@ennreal.mul_top b],
      split_ifs with hb,
      { subst hb,
        change a ≤ ⊥ at hab,
        rw le_bot_iff at hab,
        simp [hab], },
      { exact le_top, } },
    { rwa ennreal.mul_le_mul_right hc0 hctop }, },
end

lemma ennreal.mul_le_mul_of_left {a b c : ℝ≥0∞} (hab : a ≤ b) : c * a ≤ c * b :=
begin
  rw [mul_comm, mul_comm c],
  exact ennreal.mul_le_mul_of_right hab,
end

lemma nnreal.inv_mul_le_iff {a b c : ℝ≥0} (hb0 : b ≠ 0) : b⁻¹ * a ≤ c ↔ a ≤ b * c :=
begin
  rw ← nnreal.coe_le_coe,
  rw ← nnreal.coe_le_coe,
  push_cast,
  apply inv_mul_le_iff,
  obtain (hb | (hb : 0 < b)) := eq_zero_or_pos,
  { subst hb, exfalso, apply hb0, refl, },
  { assumption_mod_cast, }
end

lemma ennreal.inv_mul_le_iff {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hb : b ≠ ∞) :
  b⁻¹ * a ≤ c ↔ a ≤ b * c :=
begin
  rcases eq_or_ne c ⊤ with (rfl | hctop),
  { rw ennreal.mul_top,
    rw if_neg hb0,
    simp },
  rcases eq_or_ne a ⊤ with (rfl | hatop),
  { rw ennreal.mul_top,
    rw if_neg,
    { simp only [hctop, top_le_iff, with_top.mul_eq_top_iff, and_false, false_or, false_iff,
        not_and, not_not],
      rintro rfl,
      exact false.elim (hb rfl) },
    { intro hbinv,
      rw ennreal.inv_eq_zero at hbinv,
      subst hbinv,
      exact false.elim (hb rfl) } },
  have hbne : b.to_nnreal ≠ 0,
    apply (ennreal.to_nnreal_pos hb0 hb).ne',
  rw [← ennreal.coe_to_nnreal hctop, ← ennreal.coe_to_nnreal hatop, ← ennreal.coe_to_nnreal hb,
    ← ennreal.coe_inv hbne],
  norm_cast,
  apply nnreal.inv_mul_le_iff hbne,
end

lemma ennreal.zero_le (a : ℝ≥0∞) : 0 ≤ a := bot_le
lemma ennreal.zero_le' {a : ℝ≥0∞} : 0 ≤ a := bot_le

lemma ennreal.inv_eq_of_mul_eq_one {a b : ℝ≥0∞} (h : a * b = 1) : a⁻¹ = b :=
begin
  induction b using with_top.rec_top_coe,
  { exfalso,
    rw ennreal.mul_top at h,
    split_ifs at h with ha;
    { revert h, norm_num, }, },
  induction a using with_top.rec_top_coe,
  { exfalso,
    rw ennreal.top_mul at h,
    split_ifs at h with ha;
    { revert h, norm_num, }, },
  norm_cast at h,
  have ha : a ≠ 0,
  { rintro rfl, rw zero_mul at h, revert h, norm_num, },
  rw ← ennreal.coe_inv ha,
  norm_cast,
  rwa [← inv_mul_eq_one₀, inv_inv],
  exact inv_ne_zero ha,
end


-- lemma ennreal.top_zpow (n : ℤ) : (⊤ : ℝ≥0∞) ^ n = if n < 0 then 0 else if n = 0 then 1 else ⊤ :=
-- begin
--   have : (⊤ : ℝ≥0∞) ^ (0 : ℤ) = 1,
--     exact zpow_zero ⊤,
--   have : (⊤ : ℝ≥0∞) ^ (1 : ℤ) = ⊤,
--     exact zpow_one ⊤,
--   have : (⊤ : ℝ≥0∞) ^ (-1 : ℤ) = 0,
--     rw zpow_neg_one,
--     exact ennreal.inv_top,
--   sorry,
-- end
