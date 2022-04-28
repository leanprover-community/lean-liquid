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
--   sorry,
-- end
