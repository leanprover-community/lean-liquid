import analysis.normed_space.lp_space
import topology.instances.real
import banach

open_locale nnreal big_operators uniformity topological_space

noncomputable theory

namespace pBanach

@[derive (module ℝ)]
def lp_type (p : ℝ≥0) := lp (λ n : ℕ, ℝ) p

variable (p : ℝ≥0)

instance : has_coe_to_fun (lp_type p) (λ f, ℕ → ℝ) :=
by { dsimp [lp_type], apply_instance }

instance : has_nnnorm (lp_type p) := has_nnnorm.mk $
λ f, ∑' n : ℕ, ∥ f n ∥₊^(p : ℝ)

@[simps]
instance : has_norm (lp_type p) := has_norm.mk $
λ f, ∑' n : ℕ, ∥ f n ∥^(p : ℝ)

variables {p} [fact (0 < p)]

lemma lp_type.summable (f : lp_type p) :
  summable (λ n, | f n |^(p : ℝ)) :=
begin
  have := f.2, dsimp [lp_type, lp, mem_ℓp] at this,
  rw if_neg at this, rwa if_neg at this,
  { exact ennreal.coe_ne_top },
  { refine (ne_of_gt _),
    exact_mod_cast (fact.out (0 < p)) },
end

variables [fact (p ≤ 1)]

lemma lp_type.triangle (f g : lp_type p) :
  ∥ f + g ∥ ≤ ∥ f ∥ + ∥ g ∥ :=
begin
  dsimp,
  have : ∀ n, |f n + g n| ^ (p : ℝ) ≤ | f n | ^(p : ℝ) + |g n|^(p : ℝ),
  { intros n,
    suffices : ∥f n + g n∥₊ ^ (p : ℝ) ≤ ∥ f n ∥₊ ^(p : ℝ) + ∥ g n ∥₊^(p : ℝ),
    { exact_mod_cast this },
    refine le_trans _ (nnreal.rpow_add_le_add_rpow _ _ _ _),
    apply nnreal.rpow_le_rpow, apply nnnorm_add_le,
    refine (le_of_lt _), any_goals { exact_mod_cast (fact.out (0 < p)) },
    exact_mod_cast (fact.out (p ≤ 1)) },
  refine le_trans (tsum_le_tsum this _ _) (le_of_eq _),
  { have hh := lp_type.summable (f + g), dsimp at hh, exact hh },
  { apply summable.add,
    exact lp_type.summable f,
    exact lp_type.summable g },
  apply tsum_add,
  exact lp_type.summable f,
  exact lp_type.summable g,
end

instance : pseudo_metric_space (lp_type p) :=
{ dist := λ f g, ∥ f - g ∥,
  dist_self := begin
    have : (p : ℝ) ≠ (0 : ℝ),
    { refine ne_of_gt _, exact_mod_cast (fact.out (0 < p)) },
    intros f, dsimp,
    simp only [abs_zero, sub_self, real.zero_rpow this, tsum_zero],
  end,
  dist_comm := begin
    intros f g, dsimp,
    have : ∀ n, | f n - g n | = | g n - f n |,
    { intros n,
      rw [← neg_neg (f n - g n), abs_neg, neg_sub] },
    simp_rw this,
  end,
  dist_triangle := begin
    intros f g h,
    have := lp_type.triangle (f - g) (g - h),
    rw (show f - g + (g - h) = f - h, by abel) at this,
    exact this,
  end }

variable (p)
def has_p_norm : has_p_norm (lp_type p) p :=
{ norm_smul := begin
    intros a f, dsimp,
    have : ∀ n, |a * f n|^(p : ℝ) = |a|^(p : ℝ) * |f n|^(p : ℝ),
    { intros n, rw [abs_mul, real.mul_rpow],
      any_goals { exact abs_nonneg _ } },
    simp_rw this,
    rw tsum_mul_left,
  end,
  triangle := begin
    intros f g, apply lp_type.triangle,
  end,
  uniformity := rfl,
  ..(infer_instance : has_norm (lp_type p)) } .

instance : normed_add_comm_group (lp_type p) :=
normed_add_comm_group.of_core _
{ norm_eq_zero_iff := begin
    intros f, dsimp, split,
    { intros hf,
      ext n, suffices : | f n |^(p : ℝ) = 0,
      { rw real.rpow_eq_zero_iff_of_nonneg at this,
        simpa using this.1,
        apply abs_nonneg },
      refine le_antisymm (le_trans _ (le_of_eq hf)) _,
      { apply le_tsum (lp_type.summable f) n,
        intros m hm, dsimp,
        apply real.rpow_nonneg_of_nonneg,
        exact abs_nonneg _, },
      { apply real.rpow_nonneg_of_nonneg, apply abs_nonneg } },
    { intros hf, rw hf,
      simp only [lp.coe_fn_zero, pi.zero_apply, abs_zero],
      rw real.zero_rpow, simp only [tsum_zero],
      refine ne_of_gt _,
      exact_mod_cast (fact.out (0 < p)) }
  end,
  triangle := λ f g, has_p_norm.triangle (has_p_norm p) f g,
  norm_neg := λ f, by { dsimp, simp } }

.

lemma has_continuous_smul_δ_aux₁ (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), A * δ < ε :=
begin
  --TODO: Golf!
  by_cases hhA : A = 0,
  { use 1, split, linarith, simp [hhA], assumption },
  use ε/(2 * A), split,
  have : ε / (2 * A) = (2 * A)⁻¹ * ε, by field_simp, rw this, clear this,
  apply mul_pos,
  simp only [mul_inv_rev, zero_lt_mul_right, inv_pos, zero_lt_bit0, zero_lt_one],
  exact (ne.symm hhA).lt_of_le hA, assumption,
  rw (show A * (ε / (2 * A)) = ε/2, by { field_simp, ring }), linarith,
end

lemma has_continuous_smul_δ_aux₂ (ε : ℝ) (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), δ^((p : ℝ) + 1) < ε :=
begin
  --TODO: Golf!
  use (ε/2)^(1/((p : ℝ)+1)), split,
  { apply real.rpow_pos_of_pos, linarith },
  { rw ← real.rpow_mul,
    have : 1 / ((p : ℝ) + 1) * (p + 1) = 1,
    { have : (p : ℝ)+1 ≠ 0,
      { apply ne_of_gt,
        have : 0 < (p : ℝ) := by exact_mod_cast (fact.out (0 < p)),
        linarith },
      field_simp },
    rw [this, real.rpow_one], linarith, linarith, }
end

lemma has_continuous_smul_δ_aux₃ (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), δ^(p : ℝ) * B < ε :=
begin
  --TODO: Golf!
  by_cases hhB : B = 0,
  { use 1, split, simp, simp [hhB], assumption },
  use (ε/(2 * B))^(1/(p : ℝ)),
  split,
  { apply real.rpow_pos_of_pos,
    have : ε / (2 * B) = (2 * B)⁻¹ * ε, by field_simp, rw this, clear this,
    apply mul_pos,
    simp only [mul_inv_rev, zero_lt_mul_right, inv_pos, zero_lt_bit0, zero_lt_one],
    exact (ne.symm hhB).lt_of_le hB, assumption },
  { rw ← real.rpow_mul,
    have : 1 / (p : ℝ) * p = 1,
    { have : (p : ℝ) ≠ 0,
      { apply ne_of_gt, exact_mod_cast (fact.out (0 < p)) },
      field_simp },
    rw [this, real.rpow_one],
    rw (show ε / (2 * B) * B = ε/2, by field_simp; ring), linarith,
    have : ε / (2 * B) = (2 * B)⁻¹ * ε, by field_simp, rw this, clear this,
    apply mul_nonneg,
    simp only [mul_inv_rev, zero_le_mul_right, inv_pos, zero_lt_bit0, zero_lt_one, inv_nonneg],
    assumption,
    exact (le_of_lt hε) }
end

lemma has_continuous_smul_δ_aux (A B ε : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), A * δ + δ^(p : ℝ) * (δ + B) < ε :=
begin
  --TODO: Golf!
  have hh : 0 < ε/3, by linarith,
  obtain ⟨δ₁,hδ₁,Hδ₁⟩ := has_continuous_smul_δ_aux₁ A _ hA hh,
  obtain ⟨δ₂,hδ₂,Hδ₂⟩ := has_continuous_smul_δ_aux₂ p _ hh,
  obtain ⟨δ₃,hδ₃,Hδ₃⟩ := has_continuous_smul_δ_aux₃ p B _ hB hh,
  refine ⟨δ₁ ⊓ δ₂ ⊓ δ₃,_,_⟩,
  { rw lt_inf_iff,
    split,
    rw lt_inf_iff,
    split,
    assumption' },
  { rw mul_add,
    have : ε = ε/3 + ε/3 + ε/3, { field_simp, ring },
    rw this, clear this,
    simp only [← add_assoc],
    apply add_lt_add,
    apply add_lt_add,
    { refine lt_of_le_of_lt _ Hδ₁,
      apply mul_le_mul (le_refl _),
      rw inf_assoc,
      apply inf_le_left,
      rw le_inf_iff, split,
      rw le_inf_iff, split,
      all_goals { assumption <|> { apply le_of_lt, assumption } } },
    { have : (δ₁ ⊓ δ₂ ⊓ δ₃) ^ (p : ℝ) * (δ₁ ⊓ δ₂ ⊓ δ₃) =
        (δ₁ ⊓ δ₂ ⊓ δ₃) ^ ((p : ℝ) + 1),
      { rw [real.rpow_add, real.rpow_one],
        rw lt_inf_iff, split,
        rw lt_inf_iff, split,
        assumption' },
      rw this, clear this,
      refine lt_of_le_of_lt _ Hδ₂,
      apply real.rpow_le_rpow,
      rw le_inf_iff, split,
      rw le_inf_iff, split,
      { apply le_of_lt, assumption },
      { apply le_of_lt, assumption },
      { apply le_of_lt, assumption },
      rw [inf_comm, ← inf_assoc], exact inf_le_right,
      have : 0 < (p : ℝ) := by exact_mod_cast (fact.out (0 < p)),
      linarith },
    { refine lt_of_le_of_lt _ Hδ₃,
      apply mul_le_mul,
      { apply real.rpow_le_rpow,
        rw le_inf_iff, split,
        rw le_inf_iff, split,
        { apply le_of_lt, assumption },
        { apply le_of_lt, assumption },
        { apply le_of_lt, assumption },
        exact inf_le_right,
        apply le_of_lt,
        exact_mod_cast (fact.out (0 < p)) },
      { exact le_refl _ },
      { assumption },
      { apply real.rpow_nonneg_of_nonneg, apply le_of_lt, assumption } } }
end


instance : has_continuous_smul ℝ (lp_type p) :=
begin
  constructor,
  rw metric.continuous_iff,
  rintros ⟨a,f⟩ ε hε,
  obtain ⟨δ,hδ,Hδ⟩ : ∃ (δ : ℝ) (hδ : 0 < δ),
    |a|^(p : ℝ) * δ + δ^(p : ℝ) * (δ + ∥ f ∥) < ε,
  { apply has_continuous_smul_δ_aux,
    apply real.rpow_nonneg_of_nonneg, exact abs_nonneg _,
    exact norm_nonneg _,
    exact hε },
  refine ⟨δ,hδ,_⟩,
  rintros ⟨b,g⟩ (h : max _ _ < _), dsimp only [has_dist.dist] at h ⊢,
  refine lt_trans _ Hδ,
  rw [← norm_neg, neg_sub],
  have : ∥a • f - b • g∥ ≤ ∥ a • f - a • g ∥ + ∥ a • g - b • g ∥,
  { refine le_trans (le_of_eq _) (norm_add_le _ _),
    congr' 1, abel },
  refine lt_of_le_of_lt this _, clear this,
  apply add_lt_add_of_le_of_lt,
  { rw [← smul_sub, (has_p_norm p).norm_smul a (f - g)],
    apply mul_le_mul, exact le_refl _,
    rw [← neg_neg (f - g), norm_neg, neg_sub],
    refine le_trans (le_max_right _ _) (le_of_lt h),
    exact norm_nonneg (f - g),
    apply real.rpow_nonneg_of_nonneg, exact abs_nonneg _ },
  { rw [← sub_smul, (has_p_norm p).norm_smul (a - b) g, smul_eq_mul],
    apply mul_lt_mul',
    { apply real.rpow_le_rpow,
      exact abs_nonneg _,
      refine le_trans _ (le_of_lt h),
      rw [← neg_neg (a - b), abs_neg, neg_sub],
      exact le_max_left _ _,
      refine le_of_lt (by exact_mod_cast (fact.out (0 < p))) },
    { rw (show g = (g - f) + f, by abel),
      refine lt_of_le_of_lt (norm_add_le _ _) _,
      refine add_lt_add_of_lt_of_le _ (le_refl _),
      refine lt_of_le_of_lt (le_max_right _ _) h },
    { exact norm_nonneg _ },
    { have : (0 : ℝ) = 0^(p : ℝ),
      { rw real.zero_rpow,
        refine ne_of_gt (by exact_mod_cast (fact.out (0 < p))) },
      rw this, clear this,
      apply real.rpow_lt_rpow,
      exact le_refl _,
      exact hδ,
      exact_mod_cast (fact.out (0 < p)) } }
end

lemma uniform_continuous_coe :
  uniform_continuous (λ f n, f n : lp_type p → ℕ → ℝ) :=
begin
  rw uniform_continuous_pi, intros i,
  rw normed_add_comm_group.uniformity_basis_dist.uniform_continuous_iff
    normed_add_comm_group.uniformity_basis_dist,
  intros ε hε, dsimp,
  refine ⟨ε^(p : ℝ), _, _⟩,
  { apply real.rpow_pos_of_pos, assumption },
  rintros f g (hfg : ∥f - g∥ < ε^_),
  suffices : |f i - g i|^(p : ℝ) < ε^(p : ℝ),
  { rw real.rpow_lt_rpow_iff at this, assumption, exact abs_nonneg _, exact le_of_lt hε,
    exact_mod_cast (fact.out (0 < p)) },
  refine lt_of_le_of_lt _ hfg,
  apply le_tsum (lp_type.summable (f - g)) i,
  intros j _, apply real.rpow_nonneg_of_nonneg, exact abs_nonneg _,
end

instance : complete_space (lp_type p) :=
begin
  apply metric.complete_of_cauchy_seq_tendsto,
  intros u hu,
  obtain ⟨f, hf⟩ := cauchy_seq_tendsto_of_complete
    ((uniform_continuous_coe p).comp_cauchy_seq hu),
  have hf' : mem_ℓp f p, sorry,
  refine ⟨⟨f,hf'⟩, _⟩,
  rw metric.nhds_basis_closed_ball.tendsto_right_iff,
  intros ε hε,
  sorry
end

lemma p_banach : p_banach (lp_type p) p :=
{ exists_p_norm := nonempty.intro $ has_p_norm p }

def lp (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] : pBanach p :=
{ V := lp_type p,
  p_banach' := p_banach p }

end pBanach
