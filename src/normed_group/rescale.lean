import polyhedral_lattice.rescale
import locally_constant.Vhat

import for_mathlib.preadditive_category
import for_mathlib.additive_functor

import facts.nnreal

noncomputable theory

open_locale nnreal

namespace NormedGroup

variables (r r₁ r₂ : ℝ≥0) [fact (0 < r)] [fact (0 < r₁)] [fact (0 < r₂)]

@[simps]
def rescale (r : ℝ≥0) [fact (0 < r)] : NormedGroup ⥤ NormedGroup :=
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
      swap, { assumption },
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
    have : 0 < r₁, assumption, exact this.ne'
  end,
  naturality' := λ V W f, rfl /- defeq abuse -/ }

lemma scale_bound_by (V : NormedGroup) : ((scale r₁ r₂).app V).bound_by (r₁ / r₂) :=
normed_group_hom.mk_normed_group_hom'_bound_by _ _ _

end NormedGroup
