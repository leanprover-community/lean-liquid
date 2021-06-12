import analysis.normed_space.normed_group_hom
import topology.algebra.normed_group
import analysis.specific_limits

import for_mathlib.normed_group

noncomputable theory

open_locale filter topological_space big_operators
open set normed_group_hom uniform_space filter finset

def normed_group_hom.surjective_on_with {G H : Type*} [semi_normed_group G] [semi_normed_group H]
  (f : normed_group_hom G H) (K : add_subgroup H) (C : ℝ) : Prop :=
 ∀ h ∈ K, ∃ g, f g = h ∧ ∥g∥ ≤ C*∥h∥

variables {G : Type*} [normed_group G]
variables {H : Type*} [normed_group H]

lemma controlled_closure_of_complete [complete_space G] {f : normed_group_hom G H} {K : add_subgroup H}
  {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) (hyp : f.surjective_on_with K C) :
  f.surjective_on_with K.topological_closure (C + ε) :=
begin
  intros h h_in,
  by_cases hyp_h : h = 0,
  { rw hyp_h,
    use 0,
    simp },
  set b : ℕ → ℝ := λ i, (1/2)^i*(ε*∥h∥/2)/C,
  have b_pos : ∀ i, 0 < b i,
  { intro i,
    field_simp [b, hC],
    exact div_pos (mul_pos hε (norm_pos_iff.mpr hyp_h)) (mul_pos (by norm_num : (0 : ℝ) < 2^i*2) hC) },
  obtain ⟨v : ℕ → H, lim_v : tendsto (λ (n : ℕ), ∑ k in range (n + 1), v k) at_top (𝓝 h),
    v_in : ∀ n, v n ∈ K, hv₀ : ∥v 0 - h∥ < b 0, hv : ∀ n > 0, ∥v n∥ < b n⟩ :=
    controlled_sum_of_mem_closure h_in b_pos,
  have : ∀ n, ∃ m' : G, f m' = v n ∧ ∥m'∥ ≤ C * ∥v n∥,
  exact λ (n : ℕ), hyp (v n) (v_in n),
  choose u hu hnorm_u using this,
  set s : ℕ → G := λ n, ∑ k in range (n+1), u k,
  have : cauchy_seq s,
  { apply normed_group.cauchy_series_of_le_geometric'' (by norm_num) one_half_lt_one,
    rintro n (hn : n ≥ 1),
    calc ∥u n∥ ≤ C*∥v n∥ : hnorm_u n
    ... ≤ C * b n : mul_le_mul_of_nonneg_left (hv _ $ nat.succ_le_iff.mp hn).le hC.le
    ... = (1/2)^n * (ε * ∥h∥/2) : by simp [b, mul_div_cancel' _ hC.ne.symm]
    ... = (ε * ∥h∥/2) * (1/2)^n : mul_comm _ _ },
  obtain ⟨g : G, hg⟩ := cauchy_seq_tendsto_of_complete this,
  refine ⟨g, _, _⟩,
  { apply tendsto_nhds_unique _ lim_v,
    convert (f.continuous.tendsto g).comp hg,
    ext n,
    simp [f.map_sum, hu] },
  { suffices : ∀ n, ∥s n∥ ≤ (C + ε) * ∥h∥,
      from le_of_tendsto' (continuous_norm.continuous_at.tendsto.comp hg) this,
    intros n,
    have hnorm₀ : ∥u 0∥ ≤ C*b 0 + C*∥h∥,
    { have := calc
      ∥v 0∥ ≤ ∥h∥ + ∥v 0 - h∥ : norm_le_insert' _ _
      ... ≤ ∥h∥ + b 0 : by apply add_le_add_left hv₀.le,
      calc ∥u 0∥ ≤ C*∥v 0∥ : hnorm_u 0
      ... ≤ C*(∥h∥ + b 0) : mul_le_mul_of_nonneg_left this hC.le
      ... = C * b 0 + C * ∥h∥ : by rw [add_comm, mul_add] },
    have : ∑ k in range (n + 1), C * b k ≤ ε * ∥h∥,
    { calc ∑ k in range (n + 1), C * b k = (∑ k in range (n + 1), (1 / 2) ^ k) * (ε * ∥h∥ / 2) : by simp only [b, mul_div_cancel' _ hC.ne.symm, ← sum_mul]
      ... ≤  2 * (ε * ∥h∥ / 2) : mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (by nlinarith [hε, norm_nonneg h])
      ... = ε * ∥h∥ : mul_div_cancel' _ two_ne_zero },
    calc ∥s n∥ ≤ ∑ k in range (n+1), ∥u k∥ : norm_sum_le _ _
    ... = ∑ k in range n, ∥u (k + 1)∥ + ∥u 0∥ : sum_range_succ' _ _

    ... ≤ ∑ k in range n, C*∥v (k + 1)∥ + ∥u 0∥ : add_le_add_right (sum_le_sum (λ _ _, hnorm_u _)) _
    ... ≤ ∑ k in range n, C*b (k+1) + (C*b 0 + C*∥h∥) :  add_le_add (sum_le_sum (λ k _, _)) hnorm₀
    ... = ∑ k in range (n+1), C*b k + C*∥h∥ :  _
    ... ≤ (C+ε)*∥h∥ : _,
    { exact mul_le_mul_of_nonneg_left (hv _ k.succ_pos).le hC.le },
    { rw [← add_assoc, sum_range_succ'] },
    { rw [add_comm, add_mul],
      apply add_le_add_left this } }
end

lemma controlled_closure_range_of_complete [complete_space G] {f : normed_group_hom G H}
  {K : Type*} [semi_normed_group K] {j : normed_group_hom K H} (hj : ∀ x, ∥j x∥ = ∥x∥)
  {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) (hyp : ∀ k, ∃ g, f g = j k ∧ ∥g∥ ≤ C*∥k∥) :
  ∀ {h}, h ∈ j.range.topological_closure → ∃ g, f g = h ∧ ∥g∥ ≤ (C + ε)*∥h∥ :=
begin
  replace hyp : ∀ h ∈ j.range, ∃ g, f g = h ∧ ∥g∥ ≤ C*∥h∥,
  { intros h h_in,
    rcases (j.mem_range _).mp h_in with ⟨k, rfl⟩,
    rw hj,
    exact hyp k },
  exact controlled_closure_of_complete hC hε hyp
end

namespace normed_group_hom

variables {V₁ V₂ V₃ : Type*} [semi_normed_group V₁] [semi_normed_group V₂] [semi_normed_group V₃]
variables {f : normed_group_hom V₁ V₂} {g : normed_group_hom V₂ V₃}

--This is in #7860
lemma norm_noninc_iff_norm_le_one : f.norm_noninc ↔ ∥f∥ ≤ 1 :=
begin
  refine ⟨λ h, _, λ h, λ v, _⟩,
  { refine op_norm_le_bound _ (zero_le_one) (λ v, _),
    simpa [one_mul] using h v },
  { simpa using le_of_op_norm_le f h v }
end

--#7875
lemma comp_assoc {V₄: Type* } [semi_normed_group V₄] (h : normed_group_hom V₃ V₄)
  (g : normed_group_hom V₂ V₃) (f : normed_group_hom V₁ V₂) :
  (h.comp g).comp f = h.comp (g.comp f) :=
by { ext, refl }

--#7875
lemma norm_comp_le_of_le {C₁ C₂ : ℝ} (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) :
  ∥g.comp f∥ ≤ C₂ * C₁ :=
le_trans (norm_comp_le g f) $ mul_le_mul hg hf (norm_nonneg _) (le_trans (norm_nonneg _) hg)

--#7875
lemma norm_comp_le_of_le' (C₁ C₂ C₃ : ℝ) (h : C₃ = C₂ * C₁) (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) :
  ∥g.comp f∥ ≤ C₃ :=
by { rw h, exact norm_comp_le_of_le hg hf }

end normed_group_hom

namespace SemiNormedGroup

end SemiNormedGroup
