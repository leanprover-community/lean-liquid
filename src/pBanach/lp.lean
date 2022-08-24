import analysis.normed_space.lp_space
import topology.instances.real
import banach

open_locale nnreal big_operators

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

instance : has_continuous_smul ℝ (lp_type p) :=
begin
  constructor,
  rw metric.continuous_iff,
  rintros ⟨a,f⟩ ε hε,
  obtain ⟨δ,hδ,Hδ⟩ : ∃ (δ : ℝ) (hδ : 0 < δ),
    |a|^(p : ℝ) * δ + δ^(p : ℝ) * (δ + ∥ f ∥) < ε,
  { sorry },
  refine ⟨δ,hδ,_⟩,
  rintros ⟨b,g⟩ (h : max _ _ < _), dsimp only [has_dist.dist] at h ⊢,
  refine lt_trans _ Hδ,
  rw [← norm_neg, neg_sub],
  have : ∥a • f - b • g∥ ≤ ∥ a • f - a • g ∥ + ∥ a • g - b • g ∥,
  { refine le_trans (le_of_eq _) (norm_add_le _ _),
    congr' 1, abel },
  refine lt_of_le_of_lt this _, clear this,
  sorry,
end

instance : complete_space (lp_type p) :=
sorry

lemma p_banach : p_banach (lp_type p) p :=
{ exists_p_norm := nonempty.intro $ has_p_norm p }

def lp (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] : pBanach p :=
{ V := lp_type p,
  p_banach' := p_banach p }

end pBanach
