import for_mathlib.uniform_space_cauchy
import for_mathlib.big_operators_basic
import for_mathlib.normed_group_hom_completion
import for_mathlib.specific_limit

noncomputable theory

open filter set function normed_group uniform_space normed_group_hom finset
open_locale topological_space big_operators

lemma controlled_exactness {M M₁ M₂ : Type*} [normed_group M] [normed_group M₁] [normed_group M₂]
  {f : normed_group_hom M₁ M} {C : ℝ} (hC : 0 < C) {D : ℝ}
  {g : normed_group_hom M M₂}
  (h : ∀ m ∈ g.ker, ∃ m' : M₁, f m' = m ∧ ∥m'∥ ≤ C*∥m∥)
  (h' : ∀ x ∈ g.range, ∃ y, g y = x ∧ ∥y∥ ≤ D * ∥x∥) :
  ∀ m ∈ g.completion.ker, ∀ ε > 0, ∃ m' : completion M₁, f.completion m' = m ∧ ∥m'∥ ≤ (C + ε)*∥m∥ :=
begin
  intros hatm hatm_in ε ε_pos,
  by_cases H : hatm = 0,
  { use 0,
    simp [H] },
  set hatf := f.completion,
  set i := incl g.ker,

  have norm_j_comp_i : ∀ x, ∥j.comp i x∥ = ∥x∥,
  { intro x,
    erw [norm_to_compl, norm_incl] },
  have : hatm ∈ closure ((j.comp i).range : set $ completion M),
    by rwa ← normed_group_hom.ker_completion h',

  set b : ℕ → ℝ := λ i, (1/2)^i*(ε*∥hatm∥/2)/C,
  have b_pos : ∀ i, 0 < b i,
  { intro i,
    field_simp [b, hC],
    exact div_pos (mul_pos ε_pos (norm_pos_iff.mpr H)) (mul_pos (by norm_num : (0 : ℝ) < 2^i*2) hC) },
  obtain  ⟨m, lim_m : tendsto (λ n, ∑ k in range (n + 1), j.comp i (m k)) at_top (𝓝 hatm),
        hm₀ : ∥j.comp i (m 0) - hatm∥ < b 0, hm : ∀ n > 0, ∥(j.comp i) (m n)∥ < b n⟩ :=
    controlled_sum_of_mem_closure_range this b_pos,
  have : ∀ n, ∃ m' : M₁, f m' = m n ∧ ∥m'∥ ≤ C * ∥m n∥,
  { intros n, apply h, exact (m n).property },
  choose m' hfm' hnorm_m' using this,
  set s : ℕ → completion M₁ := λ n, ∑ k in range (n+1), j (m' k),
  have : cauchy_seq s,
  { apply normed_group.cauchy_series_of_le_geometric'' (by norm_num) one_half_lt_one,
    rintro n (hn : n ≥ 1),
    calc ∥j (m' n)∥ = ∥m' n∥ : norm_to_compl _
    ... ≤ C*∥m n∥ : hnorm_m' n
    ... = C*∥j.comp i (m n)∥ : by rw norm_j_comp_i
    ... ≤ C * b n : mul_le_mul_of_nonneg_left (hm _ $ nat.succ_le_iff.mp hn).le hC.le
    ... = (1/2)^n * (ε * ∥hatm∥/2) : by simp [b, mul_div_cancel' _ hC.ne.symm]
    ... = (ε * ∥hatm∥/2) * (1/2)^n : mul_comm _ _ },
  obtain ⟨hatm' : completion M₁, hhatm'⟩ := cauchy_seq_tendsto_of_complete this,
  refine ⟨hatm', _, _⟩,
  { apply tendsto_nhds_unique _ lim_m,
    convert (hatf.continuous.tendsto hatm').comp hhatm',
    ext n,
    dsimp [s],
    rw [hatf.map_sum],
    congr,
    ext k,
    erw [f.completion_coe, hfm'],
    refl },
  { apply le_of_tendsto' (continuous_norm.continuous_at.tendsto.comp hhatm'),
    simp only [norm_j_comp_i] at hm,
    have hnorm₀ : ∥j (m' 0)∥ ≤ C*b 0 + C*∥hatm∥,
    { have := calc
      ∥m 0∥ = ∥j.comp i (m 0)∥ : by rw norm_j_comp_i
      ... ≤ ∥hatm∥ + ∥j.comp i (m 0) - hatm∥ : norm_le_insert' _ _
      ... ≤ ∥hatm∥ + b 0 : by apply add_le_add_left hm₀.le,

      calc ∥j (m' 0)∥  = ∥m' 0∥ : norm_to_compl _
      ... ≤ C*∥m 0∥ : hnorm_m' 0
      ... ≤ C*(∥hatm∥ + b 0) : mul_le_mul_of_nonneg_left this hC.le
      ... = C * b 0 + C * ∥hatm∥ : by rw [add_comm, mul_add] },

    intros n,
    have : ∑ k in range (n + 1), C * b k ≤ ε * ∥hatm∥,
    calc ∑ k in range (n + 1), C * b k = (∑ k in range (n + 1), (1 / 2) ^ k) * (ε * ∥hatm∥ / 2) : by simp only [b, mul_div_cancel' _ hC.ne.symm, ← sum_mul]
     ... ≤  2 * (ε * ∥hatm∥ / 2) : mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (by nlinarith [ε_pos, norm_nonneg hatm])
     ... = ε * ∥hatm∥ : mul_div_cancel' _ two_ne_zero,

    calc ∥s n∥ ≤ ∑ k in range (n+1), ∥j (m' k)∥ : norm_sum_le _ _
    ... = ∑ k in range n, ∥j (m' (k + 1))∥ + ∥j (m' 0)∥ : sum_range_succ' _ _
    ... = ∑ k in range n, ∥m' (k + 1)∥ + ∥j (m' 0)∥ : by simp only [norm_to_compl]
    ... ≤ ∑ k in range n, C*∥m (k + 1)∥ + ∥j (m' 0)∥ : add_le_add_right (sum_le_sum (λ _ _, hnorm_m' _)) _
    ... ≤ ∑ k in range n, C*b (k+1) + (C*b 0 + C*∥hatm∥) :  add_le_add (sum_le_sum (λ k _, _)) hnorm₀
    ... = ∑ k in range (n+1), C*b k + C*∥hatm∥ :  _
    ... ≤ (C+ε)*∥hatm∥ : _,

    { exact mul_le_mul_of_nonneg_left (hm _ k.succ_pos).le hC.le },
    { rw [← add_assoc, sum_range_succ'] },
    { rw [add_comm, add_mul],
      apply add_le_add_left this } }
end
