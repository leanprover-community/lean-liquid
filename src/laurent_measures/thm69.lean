import category_theory.Fintype
import data.real.nnreal
import laurent_measures.basic
import order.filter.at_top_bot

/-
We define the map θ : (laurent_measures r `singleton`) → ℝ and we show it is surjective.
TO DO :
* Prove `lemma has_sum_pow_floor` and deduce `lemma has_sum_pow_floor_norm` from it
* Upgrade θ to a `comp_haus_blah` morphism
* Finish the proof of surjectivity for negative reals using linearity
-/

open filter function classical
open_locale topological_space classical nnreal

section thm69_surjective

lemma converges_floor (x : ℝ≥0) :
  tendsto (λn : ℕ, (floor (2 ^ n * x : ℝ) / (2 ^ n) : ℝ)) at_top (𝓝 x) :=
begin
  have two_pow_pos : ∀ n : ℕ,  0 < (2 ^ n : ℝ) := by simp only
    [forall_const, zero_lt_bit0, pow_pos, zero_lt_one],
  have h₁ : ∀ n : ℕ, (x.1 - 1 / 2 ^ n) ≤ (floor (2 ^ n * x : ℝ) / (2 ^ n) : ℝ),
  { intro n,
    have := (div_le_div_right $ two_pow_pos n).mpr (le_of_lt (sub_one_lt_floor (2 ^ n * x.1))),
    calc (x.1 - 1 / 2 ^ n) = ( 2 ^ n * x.1 - 1)/ 2 ^ n : by field_simp[mul_comm]
                       ... ≤ (floor (2 ^ n * x.1) / (2 ^ n)) : this },
  have HH : tendsto (λn : ℕ, (x.1 - 1 / 2 ^ n)) at_top (𝓝 x),
  { suffices : tendsto (λn : ℕ, (1 / 2 ^ n : ℝ)) at_top (𝓝 0),
    { have h_geom := tendsto.mul_const (-1 : ℝ) this,
      replace h_geom := tendsto.const_add x.1 h_geom,
      simp_rw [pi.add_apply, zero_mul, add_zero, mul_neg_one] at h_geom,
      exact h_geom },
    have abs_half : abs ((1:ℝ)/2) < 1 := by {rw [abs_div, abs_one, abs_two], exact one_half_lt_one},
    have mah := tendsto_pow_at_top_nhds_0_of_abs_lt_1 (abs_half),
    simp_rw [← one_div_pow],
    exact mah },
  have h₂ : ∀ n : ℕ, ((floor (2 ^ n * x.1) ) / (2 ^ n) : ℝ) ≤ x.1,
  { intro n,
    have := (div_le_div_right $ two_pow_pos n).mpr (floor_le (2 ^ n * x.1)),
    calc (floor (2 ^ n * x.1) / 2 ^ n : ℝ)  ≤ (2 ^ n * x.1 / 2 ^ n) : this
                                        ... = (x.1 * 2 ^ n / 2 ^ n) : by simp only [mul_comm]
                                        ... = x.1 : by simp only [mul_div_cancel_of_invertible] },
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le HH tendsto_const_nhds h₁ h₂,
end

noncomputable def sum_floor (x : ℝ≥0): ℤ → ℤ
| (int.of_nat n)          := nat.rec_on n
                          (floor x.1) (λ n, floor (2 ^ (nat.succ n) * x.1) - floor (2 ^ n * x.1))
| (int.neg_succ_of_nat n) := 0


lemma has_sum_pow_floor (r' : ℝ≥0) [fact (r' < 1)] (x : ℝ≥0) :
  has_sum (λ n, (coe ∘ sum_floor x) n * r'.1 ^ n) x.1 :=
begin
  sorry,
end

lemma has_sum_pow_floor_norm (r : ℝ≥0)  [fact (r < 1)] (x : ℝ≥0) :
  has_sum (λ n, ∥ ((coe : ℤ → ℝ) ∘ sum_floor x) n ∥ * r ^ n) x.1:=
begin
  sorry,--will be an easy consequence of the previous one
end

def laurent_measures.to_Rfct (r : ℝ≥0) [fact (r < 1)] :
  (laurent_measures r (Fintype.of punit)) → (ℤ → ℝ) := λ ⟨F, _⟩, coe ∘ (F punit.star)

noncomputable def θ (r' : ℝ≥0) [fact (r' < 1)] (r : ℝ≥0) [fact (r < 1)] :
 (laurent_measures r (Fintype.of punit)) → ℝ := λ F, tsum (λ n, (F.to_Rfct r n) * (r'.1) ^ n)

lemma θ_surj_on_nonneg (r' : ℝ≥0) [fact (r' < 1)] (r : ℝ≥0) [fact (r < 1)] (x : ℝ≥0) :
  ∃ (F : laurent_measures r (Fintype.of punit)), (θ r' r F) = x :=
begin
  let F₀ : Fintype.of punit → ℤ → ℤ := λ a, (sum_floor x),
  have Hr : ∀ (s : Fintype.of punit), summable (λ (n : ℤ), ∥F₀ s n∥ * ↑r ^ n),
  { intro s,
    apply has_sum.summable (has_sum_pow_floor_norm r x) },
  let F : laurent_measures r (Fintype.of punit) := ⟨F₀, Hr⟩,
  use F,
  have : summable (λ (n : ℤ), (F.to_Rfct r n) * (r'.1) ^ n) :=
    has_sum.summable (has_sum_pow_floor r' x),
  unfold θ,
  unfold tsum,
  rw [dif_pos this],
  exact has_sum.unique (some_spec this) (has_sum_pow_floor r' x),
end

lemma θ_surj (r' : ℝ≥0) [fact (r' < 1)] (r : ℝ≥0) [fact (r < 1)] : surjective (θ r' r) :=
begin
  intro x,
  by_cases hx : 0 ≤ x,
  { exact θ_surj_on_nonneg r' r ⟨x, hx⟩},
  replace hx := le_of_lt (neg_pos_of_neg (lt_of_not_ge hx)),
  obtain ⟨F, hF⟩ := θ_surj_on_nonneg r' r ⟨-x,hx⟩,
  use -F,
  sorry,--better to do it later, once θ becomes a comp_haus_blah morphism, in particular linear
end

end thm69_surjective
