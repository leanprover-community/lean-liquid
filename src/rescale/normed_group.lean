import rescale.basic
import locally_constant.Vhat

import for_mathlib.preadditive_category
import for_mathlib.additive_functor

import facts.nnreal

noncomputable theory
open_locale big_operators classical nnreal

local attribute [-instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

namespace rescale

variables {N : ℝ≥0} {V : Type*}

instance [has_norm V] : has_norm (rescale N V) :=
{ norm := λ v, ∥of.symm v∥/N }

lemma norm_def [has_norm V] (v : rescale N V) : ∥v∥ = ∥of.symm v∥/N := rfl

-- remove the `fact` once we have `seminormed_group`
instance [hN : fact (0 < N)] [normed_group V] : normed_group (rescale N V) :=
normed_group.of_core (rescale N V)
{ norm_eq_zero_iff := λ v,
  begin
    have aux : (N:ℝ) ≠ 0 := ne_of_gt hN.out,
    simp only [norm_def, div_eq_zero_iff, aux, or_false],
    exact norm_eq_zero -- defeq abuse
  end,
  triangle := λ v w,
  begin
    simp only [norm_def, ← add_div],
    exact div_le_div_of_le hN.out.le (norm_add_le _ _), -- defeq abuse
  end,
  norm_neg := λ v, by { simp only [norm_def], congr' 1, exact norm_neg _ /- defeq abuse -/ } }

lemma nnnorm_def [hN : fact (0 < N)] [normed_group V] (v : rescale N V) :
  nnnorm v = nnnorm (of.symm v) / N := rfl

end rescale

namespace NormedGroup

variables (r r₁ r₂ : ℝ≥0) [fact (0 < r)] [fact (0 < r₁)] [fact (0 < r₂)]

@[simps]
def rescale (r : ℝ≥0) [hr : fact (0 < r)] : NormedGroup ⥤ NormedGroup :=
{ obj := λ V, of $ rescale r V,
  map := λ V₁ V₂ f,
  { to_fun := λ v, @rescale.of r V₂ $ f ((@rescale.of r V₁).symm v),
    map_add' := f.map_add, -- defeq abuse
    bound' :=
    begin
      obtain ⟨C, C_pos, hC⟩ := f.bound,
      use C,
      dsimp,
      intro v,
      rw [rescale.norm_def, rescale.norm_def, ← mul_div_assoc, div_le_div_right],
      swap, { exact hr.out },
      exact hC _,
    end },
  map_id' := λ V, rfl, -- defeq abuse
  map_comp' := λ V₁ V₂ V₃ f g, rfl /- defeq abuse -/ }

instance rescale.additive : (rescale r).additive :=
{ map_zero' := λ V W, rfl, -- defeq abuse
  map_add' := λ V W f g, rfl /- defeq abuse -/ }

def to_rescale : 𝟭 _ ⟶ rescale r :=
{ app := λ V,
  add_monoid_hom.mk_normed_group_hom' (add_monoid_hom.mk' (@rescale.of r V) $ λ _ _, rfl) r⁻¹
  begin
    intro v,
    dsimp,
    rw [rescale.nnnorm_def, div_eq_inv_mul],
    refl
  end,
  naturality' := λ V W f, rfl /- defeq abuse -/ }

lemma to_rescale_bound_by (V : NormedGroup) : ((to_rescale r).app V).bound_by r⁻¹ :=
normed_group_hom.mk_normed_group_hom'_bound_by _ _ _

def scale : rescale r₁ ⟶ rescale r₂ :=
{ app := λ V,
  add_monoid_hom.mk_normed_group_hom'
    (add_monoid_hom.mk' (λ v, (@rescale.of r₂ V) $ (@rescale.of r₁ V).symm v) $
      λ _ _, rfl) (r₁ / r₂)
  begin
    dsimp,
    intro v,
    simp only [rescale.nnnorm_def, add_monoid_hom.coe_mk', div_eq_inv_mul, equiv.symm_apply_apply],
    rw [mul_assoc, mul_inv_cancel_left'],
    have : fact (0 < r₁), assumption, exact this.out.ne'
  end,
  naturality' := λ V W f, rfl /- defeq abuse -/ }

lemma scale_bound_by (V : NormedGroup) : ((scale r₁ r₂).app V).bound_by (r₁ / r₂) :=
normed_group_hom.mk_normed_group_hom'_bound_by _ _ _

end NormedGroup
