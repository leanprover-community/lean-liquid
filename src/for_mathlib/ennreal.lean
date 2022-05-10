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

-- could go in ennreal line 684 or so
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

-- could go in ennreal line 684 or so
lemma ennreal.mul_le_mul_of_left {a b c : ℝ≥0∞} (hab : a ≤ b) : c * a ≤ c * b :=
begin
  rw [mul_comm, mul_comm c],
  exact ennreal.mul_le_mul_of_right hab,
end

-- might not need this
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
  rw [mul_comm, mul_comm b],
  apply ennreal.div_le_iff_le_mul;
  cc,
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

lemma ennreal.mul_inv_eq_of_eq_mul {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbtop : b ≠ ⊤) (h : a = c * b) :
  a * b⁻¹ = c :=
by rw [h, mul_assoc, ennreal.mul_inv_cancel hb0 hbtop, mul_one]

lemma ennreal.eq_mul_of_mul_inv_eq {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbtop : b ≠ ⊤) (h : a * b⁻¹ = c) :
  a = c * b :=
by rw [← h, mul_assoc, ennreal.inv_mul_cancel hb0 hbtop, mul_one]

lemma ennreal.mul_eq_of_mul_inv_eq {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbtop : b ≠ ⊤) (h : a * b⁻¹ = c) :
  c * b = a :=
(ennreal.eq_mul_of_mul_inv_eq hb0 hbtop h).symm

lemma ennreal.mul_inv_eq_iff_eq_mul {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbtop : b ≠ ⊤) :
  (a * b⁻¹ = c ↔ a = c * b) :=
⟨ennreal.eq_mul_of_mul_inv_eq hb0 hbtop, ennreal.mul_inv_eq_of_eq_mul hb0 hbtop⟩

lemma ennreal.le_zero_iff {a : ℝ≥0∞} : a ≤ 0 ↔ a = 0 := le_bot_iff

lemma ennreal.sub_pos {a b : ℝ≥0∞} : 0 < a - b ↔ b < a :=
begin
  rw ← not_iff_not,
  push_neg,
  rw ennreal.le_zero_iff,
  apply tsub_eq_zero_iff_le,
end

lemma ennreal.top_zpow_of_pos {n : ℤ} (hn : 0 < n) : (⊤ : ℝ≥0∞) ^ n = ⊤ :=
begin
  let m := n.nat_abs,
  have hm : n = m,
  { rw int.nat_abs_of_nonneg hn.le },
  rw hm at hn ⊢,
  apply ennreal.top_pow,
  exact_mod_cast hn,
end

-- can't do!
--lemma ennreal.zpow_neg (a : ℝ≥0∞) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹ := sorry

-- lemma ennreal.top_zpow_of_neg {n : ℤ} (hn : n < 0) : (⊤ : ℝ≥0∞) ^ n = 0 :=
-- begin
--   let m := n.nat_abs,
--   have hm : n = -m,
--   { rw [int.of_nat_nat_abs_of_nonpos hn.le, neg_neg] },
--   rw hm at hn ⊢,
--   rw neg_lt_zero at hn,
--   have hm' : 0 < m, by exact_mod_cast hn,
--   rw [ennreal.zpow_neg, zpow_coe_nat, ennreal.inv_eq_zero, ennreal.top_pow hm'],
-- end
