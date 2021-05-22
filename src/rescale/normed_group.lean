import rescale.basic
import locally_constant.Vhat

import category_theory.preadditive.additive_functor

import facts.nnreal

noncomputable theory
open_locale big_operators classical nnreal

namespace rescale

variables {N : ℝ≥0} {V : Type*}

instance [has_norm V] : has_norm (rescale N V) :=
{ norm := λ v, ∥of.symm v∥/N }

lemma norm_def [has_norm V] (v : rescale N V) : ∥v∥ = ∥of.symm v∥/N := rfl

instance [hN : fact (0 < N)] [semi_normed_group V] : semi_normed_group (rescale N V) :=
semi_normed_group.of_core (rescale N V)
{ norm_zero := show ∥(0 : V)∥/N = 0, by rw [norm_zero, zero_div],
  triangle := λ v w,
  begin
    simp only [norm_def, ← add_div],
    exact div_le_div_of_le hN.out.le (norm_add_le _ _), -- defeq abuse
  end,
  norm_neg := λ v, by { simp only [norm_def], congr' 1, exact norm_neg _ /- defeq abuse -/ } }

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

lemma nnnorm_def [hN : fact (0 < N)] [semi_normed_group V] (v : rescale N V) :
  nnnorm v = nnnorm (of.symm v) / N := rfl

end rescale

namespace SemiNormedGroup

variables (r r₁ r₂ : ℝ≥0) [fact (0 < r)] [fact (0 < r₁)] [fact (0 < r₂)]

@[simps]
def rescale (r : ℝ≥0) [hr : fact (0 < r)] : SemiNormedGroup ⥤ SemiNormedGroup :=
{ obj := λ V, of $ rescale r V,
  map := λ V₁ V₂ f,
  { to_fun := λ v, @rescale.of r V₂ $ f ((@rescale.of r V₁).symm v),
    map_add' := f.map_add, -- defeq abuse
    bound' :=
    begin
      obtain ⟨C, C_pos, hC⟩ := f.bound,
      use C,
      intro v,
      have := hC ((@rescale.of r V₁).symm v),
      rw [← div_le_div_right (show 0 < (r:ℝ), from hr.1), mul_div_assoc] at this,
      exact this,
    end },
  map_id' := λ V, rfl, -- defeq abuse
  map_comp' := λ V₁ V₂ V₃ f g, rfl /- defeq abuse -/ }

instance rescale.additive : (rescale r).additive :=
{ map_zero' := λ V W, rfl, -- defeq abuse
  map_add' := λ V W f g, rfl /- defeq abuse -/ }

lemma rescale_map_bound_by {V₁ V₂ : SemiNormedGroup} {f : V₁ ⟶ V₂} {C : ℝ≥0} (hf : f.bound_by C) :
  ((rescale r).map f).bound_by C :=
begin
  intro v,
  dsimp,
  erw [rescale.norm_def, rescale.norm_def, equiv.symm_apply_apply, ← mul_div_assoc],
  refine div_le_div (mul_nonneg C.coe_nonneg (norm_nonneg _)) (hf _) _ le_rfl,
  rw nnreal.coe_pos, apply fact.out
end

def to_rescale : 𝟭 _ ⟶ rescale r :=
{ app := λ V,
  add_monoid_hom.mk_normed_group_hom' (add_monoid_hom.mk' (@rescale.of r V) $ λ _ _, rfl) r⁻¹
  begin
    intro v,
    rw ← div_eq_inv_mul,
    refl
  end,
  naturality' := λ V W f, rfl /- defeq abuse -/ }

def of_rescale [hr : fact (0 < r)] : rescale r ⟶ 𝟭 _ :=
{ app := λ V,
  add_monoid_hom.mk_normed_group_hom' (add_monoid_hom.mk' (@rescale.of r V) .symm $ λ _ _, rfl) r
  begin
    intro v,
    erw [rescale.nnnorm_def, mul_div_cancel' _ hr.1.ne'],
    exact le_rfl
  end,
  naturality' := λ V W f, rfl /- defeq abuse -/ }

@[simps]
def iso_rescale [fact (0 < r)] : 𝟭 _ ≅ (rescale r) :=
{ hom := to_rescale r,
  inv := of_rescale r, }

open category_theory

lemma iso_rescale_isometry [fact (0 < r)] (h : r = 1) (V : SemiNormedGroup) :
  isometry ((iso_rescale r).app V).hom :=
begin
  unfreezingI { cases h },
  dsimp only [nat_iso.app_hom, iso_rescale_hom],
  apply normed_group_hom.isometry_of_norm,
  intro v,
  erw [rescale.norm_def],
  simp only [div_one, subtype.coe_mk],
  refl
end

lemma to_rescale_bound_by (V : SemiNormedGroup) : ((to_rescale r).app V).bound_by r⁻¹ :=
normed_group_hom.mk_normed_group_hom'_bound_by _ _ _

def scale : rescale r₁ ⟶ rescale r₂ :=
{ app := λ V,
  add_monoid_hom.mk_normed_group_hom'
    (add_monoid_hom.mk' (λ v, (@rescale.of r₂ V) $ (@rescale.of r₁ V).symm v) $
      λ _ _, rfl) (r₁ / r₂)
  begin
    dsimp,
    intro v,
    apply le_of_eq,
    show _ = r₁ / r₂ * (nnnorm ((@rescale.of r₁ V).symm v) / r₁),
    simp only [add_monoid_hom.mk'_apply, div_eq_inv_mul, rescale.nnnorm_def],
    rw [mul_assoc, mul_inv_cancel_left' (show r₁ ≠ 0, from ne_of_gt $ fact.out _)],
    refl,
  end,
  naturality' := λ V W f, rfl /- defeq abuse -/ }

lemma scale_bound_by (V : SemiNormedGroup) : ((scale r₁ r₂).app V).bound_by (r₁ / r₂) :=
normed_group_hom.mk_normed_group_hom'_bound_by _ _ _

end SemiNormedGroup
