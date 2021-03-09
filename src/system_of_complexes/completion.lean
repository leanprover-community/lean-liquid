import analysis.specific_limits
import system_of_complexes.basic
import locally_constant.Vhat

open finset filter
open_locale nnreal big_operators topological_space

namespace system_of_complexes

universe variables u
variables (C C₁ C₂ : system_of_complexes.{u})
variables {k k' K K' : ℝ≥0} {m m' : ℤ} {c₀ c₀' : ℝ≥0} [fact (1 ≤ k)] [fact (1 ≤ k')]

noncomputable def completion (C : system_of_complexes) : system_of_complexes :=
sorry
-- C ⋙ NormedGroup.Completion.pushforward_homological_complex

namespace is_weak_bounded_exact

lemma controlled_y (hC : C.is_weak_bounded_exact k K m c₀) :
∀ c ≥ c₀, ∀ i < m,
∀ x : C (k^2 * c) (i+1),
∀ (ε > 0) (δ > 0), ∃ y : C c i, ∥res x - C.d _ _ y∥
                   ≤ K * ∥C.d _ (i+1) x∥ + ε ∧ ∥y∥ ≤ K*(K + 1)*∥x∥ + δ :=
sorry

lemma completion (hC : C.is_weak_bounded_exact k K m c₀) :
  C.completion.is_weak_bounded_exact (k^2) K m c₀ :=
sorry

lemma strong_of_complete (hC : C.is_weak_bounded_exact k K m c₀)
  (hC' : admissible C) [∀ c i, complete_space (C c i)] :
  ∀ δ > 0, C.is_bounded_exact (k^2) (K + δ) m c₀ :=
begin
  intros δ hδ,
  -- suffices : ∀ c ≥ c₀, ∀ i < m - 1, ∀ x : C (k * (k * c)) (i + 1 + 1), C.d _ _ x = 0 → ∃ y : C c (i + 1), res x = C.d _ _ y,
  -- { apply is_weak_bounded_exact.to_exact _ hδ,
  --   intros c hc i hi x hx,
  --   haveI : fact (k * (k * c) ≤ k ^ 2 * c) := by { show _ ≤ _, convert le_refl _ using 1, ring},
  --   rcases this c hc i hi (res x) _ with ⟨y, hy⟩,
  --   use [y, by simpa using hy],
  --   simp [C.d_res, hx],
  --   apply hC.of_le hC' _ (le_refl _) (le_refl _) (le_refl _),
  --   -- nnreal hell now
  --   have : (1 : ℝ) ≤ k, assumption,
  --   suffices : (k : ℝ) ≤ k^2, exact_mod_cast this,
  --   rw pow_two,
  --   conv_lhs { rw ← mul_one (k : ℝ) },
  --   apply mul_le_mul ; linarith },
  refine (hC.of_le hC' _ le_rfl le_rfl le_rfl).to_exact hδ _,
  { calc k = k * 1 : by rw mul_one
    ... ≤ k * k : mul_le_mul' le_rfl ‹_›
    ... = k ^ 2 : by rw pow_two },
  rintros c hc i hi x _ rfl hx,
  haveI : fact (k * c ≤ k ^ 2 * c) := by { rw [pow_two, mul_assoc], apply_instance },
  have fact₁ : k * c ≥ c₀,
  calc c₀ ≤ c : hc
  ... ≤ 1*c : by rw one_mul
  ... ≤ k*c : mul_le_mul' _inst_1 (le_refl _),
  let K' := if K = 0 then 1 else K,
  have hK' : (0 : ℝ) < K',
  { dsimp [K'],
    split_ifs,
    norm_num,
    exact zero_lt_iff.mpr h },
  let ε : ℕ → ℝ := λ j, (1/2*(1/2) ^ j) / K' / 2,
  have ε_pos : ∀ j, 0 < ε j,
  { intro j,
    dsimp [ε],
    refine div_pos (div_pos (mul_pos _ _) hK') zero_lt_two; norm_num },
  have ε_decr : ∀ j, ε (j+1) ≤ ε j,
  { intros j,
    dsimp [ε],
    field_simp,
    apply one_div_le_one_div_of_le;
    norm_num [hK', pow_succ],
    calc (2 : ℝ)^j = 1*2^j : (one_mul _).symm
       ... ≤ 2*2^j : mul_le_mul_of_nonneg_right one_le_two (pow_nonneg zero_le_two _) },
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i-1, by linarith⟩,
  have seq : ∀ j : ℕ, ∃ w : C (k*c) i, ∥res x - C.d i (i+1) w∥ ≤ ε j,
  { intro j,
    haveI : fact (k * (k * c) ≤ k ^ 2 * c) := by { show _ ≤ _, convert le_refl _ using 1, ring},
    specialize hC (k*c) fact₁ _ hi (res x) (ε j) (ε_pos j),
    obtain ⟨i', -, hi', rfl, y, hy⟩ := hC,
    simp only [d_res, res_res, normed_group_hom.map_zero, hx, norm_zero, zero_add, mul_zero] at hy,
    rw [add_left_inj] at hi',
    cases hi',
    refine ⟨y, hy⟩ },
  choose w hw using seq,
  let δ : ℕ → ℝ := λ j, 1/2*(1/2) ^ j,
  have δ_pos : ∀ j, 0 < δ j,
    by norm_num [δ],
  have hεδ : ∀ j, (K : ℝ) * (2 * ε j) + δ j ≤ 1 * (1 / 2) ^ j,
  { intro j,
    dsimp [ε, δ],
    conv_rhs { congr, rw [show (1 : ℝ) = 1/2 + 1/2, by norm_num] },
    rw add_mul (1/2 : ℝ) (1/2),
    by_cases hK : K = 0,
    { simp only [hK, div_zero, nnreal.coe_zero, zero_div, zero_add, le_add_iff_nonneg_left, mul_zero, K', if_pos, zero_mul],
      apply mul_nonneg,
      norm_num,
      apply pow_nonneg,
      norm_num },
    { apply le_of_eq,
      congr' 1,
      simp only [K', if_neg hK],
      rw [mul_div_cancel' _ (two_ne_zero : (2 : ℝ) ≠ 0),
          mul_div_cancel' _ (nnreal.coe_ne_zero.mpr hK)]} },
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i-1, by linarith⟩,
  have seq : ∀ j : ℕ, ∃ z : C c i, ∥res (w (j+1) - w j) - C.d _ _ z∥
                      ≤ K*∥C.d _ (i+1+1) (w (j+1) - w j)∥ + δ j,
  { intro j,
    obtain ⟨i', -, hi', rfl, hy⟩ := hC c hc (i+1) (by linarith) (w (j+1) - w j) _ (δ_pos j),
    rw [add_left_inj] at hi', cases hi', exact hy },
  choose z hz using seq,
  let y : ℕ → C c (i+1) := λ j, res (w j) - ∑ l in range j, C.d _ _ (z l),
  have cau_y : cauchy_seq y,
  { apply cauchy_seq_of_le_geometric (1/(2 : ℝ)) 1 (half_lt_self zero_lt_one),
    intros j,
    have fact : ∥C.d _ (i+1+1) (w (j + 1) - w j)∥ ≤ 2*ε j :=
    calc ∥C.d _ (i+1+1) (w (j + 1) - w j)∥
        = ∥(C.d _ _ (w (j + 1)) - res x) + (res x - C.d _ _ (w j))∥ : by {congr' 1, rw normed_group_hom.map_sub, abel}
    ... ≤ ∥C.d _ _ (w (j + 1)) - res x∥ + ∥res x - C.d _ _ (w j)∥ : norm_add_le _ _
    ... = ∥res x - C.d _ _ (w (j + 1))∥ + ∥res x - C.d _ _ (w j)∥ : by { rw norm_sub_rev }
    ... ≤ ε (j+1) + ε j : add_le_add (hw $ j+1) (hw j)
    ... ≤ 2*ε j : by linarith [ε_decr j],
    calc dist (y j) (y (j + 1)) = ∥y (j+1) - y j∥ : by rw dist_eq_norm'
    ... = ∥res (w (j + 1)) - res (w j) - (∑ (l : ℕ) in range (j + 1), C.d _ _ (z l)
                                - ∑ (l : ℕ) in range j, C.d _ _ (z l))∥ : by { dsimp [y], congr' 1, abel }
    ... = ∥res (w (j + 1) - (w j)) - C.d _ _ (z j)∥ : by simp [normed_group_hom.map_sub, sum_range_succ]
    ... ≤ K * ∥C.d _ _ (w (j + 1) - w j)∥ + δ j : hz j
    ... ≤ K * (2* ε j) + δ j : by {apply add_le_add_right, apply mul_le_mul_of_nonneg_left fact (nnreal.coe_nonneg K)}
    ... ≤ 1 * (1 / 2) ^ j : hεδ j },
  have hdyj : ∀ j, C.d _ _ (y j) = res (C.d _ _ $ w j),
  { intro j,
    calc C.d _ _ (y j) = C.d _ _ (res (w j) - ∑ l in range j, C.d _ (i+1) (z l)) : rfl
    ... = C.d _ _ (res (w j)) - ∑ l in range j, C.d (i+1) (i+1+1) (C.d _ _ (z l)) : by rw [normed_group_hom.map_sub, normed_group_hom.map_sum]
    ... = res (C.d _ _ (w j))  : by simp only [d_res, d_d, sum_const_zero, sub_zero] },

  have hblop : ∀ j, ∥res x - C.d _ _ (y j)∥  ≤ ε j,
  { intro j,
    calc ∥res x - C.d _ _ (y j)∥ = ∥res x - res (C.d _ _ $ w j)∥ : by rw hdyj
    ... = ∥(res (res x : C (k*c) (i+1+1)) - res (C.d _ _ $ w j) : C c _)∥ : by { rw  C.res_res }
    ... = ∥res (res x - (C.d _ _ $ w j))∥ : by rw res.map_sub
    ... ≤ ∥res x - C.d _ _ (w j)∥ : by apply hC'.res_norm_noninc
    ... ≤ ε j : hw _},

  rcases cauchy_seq_tendsto_of_complete cau_y with ⟨y₀, hy₀⟩,
  refine ⟨_, rfl, y₀, _⟩,
  apply eq_of_norm_sub_le_zero,
  have lim_norm : tendsto (λ j, ∥res x - C.d _ _ (y j)∥) at_top (𝓝 ∥res x - C.d _ _ y₀∥),
  { have cont : continuous (λ y : C c (i+1), ∥res x - C.d _ _ y∥),
      from continuous_norm.comp (continuous_const.sub $ normed_group_hom.continuous _),
    exact (cont.tendsto y₀).comp hy₀ },
  have lim_ε : tendsto ε at_top (𝓝 0),
  { rw show (0 : ℝ) = (1/2*0)/K'/2, by norm_num,
    refine (tendsto.const_mul (1 / 2) (tendsto_pow_at_top_nhds_0_of_lt_1 _ _)).div_const.div_const;
    norm_num },
  exact le_of_tendsto_of_tendsto' lim_norm lim_ε hblop,
end

end is_weak_bounded_exact

end system_of_complexes
