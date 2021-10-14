import for_mathlib.SemiNormedGroup
/-!

# Seminormed groups with an extra automorphism

This file contains definition 8.13 of `analytic.pdf`, a category-theoretic
definition of a seminormed group eqipped with an automorphism which scales
norms by a fixed factor `r`.

-/

open_locale nnreal

/-- A `normed_with_aut r V` structure on a seminormed group `V`
consists of an automorphism `T` satisfying `∥T v∥ = r * ∥v∥`.

In other words, it is a normed `ℤ[T^{±1}]`-module satisfying `∥T v∥ = r * ∥v∥`.

Definition 8.13 of [Analytic] -/
class normed_with_aut (r : out_param ℝ≥0) (V : SemiNormedGroup) :=
(T : V ≅ V)
(norm_T : ∀ v : V, ∥(T.hom : V → V) v∥ = r * ∥v∥)

variables {r : ℝ≥0} (V : SemiNormedGroup) [normed_with_aut r V] [fact (0 < r)]

namespace normed_with_aut

lemma norm_T_inv (v : V) : ∥T.inv v∥ = r⁻¹ * ∥v∥ :=
begin
  calc ∥(T.inv : V → V) v∥
      = r⁻¹ * ∥T.hom (T.inv v)∥ : _
  ... = r⁻¹ * ∥v∥ : _,
  { rw [normed_with_aut.norm_T, inv_mul_cancel_left₀],
    apply ne_of_gt,
    rw nnreal.coe_pos,
    exact ‹fact (0 < r)›.out },
  { rw [← category_theory.comp_apply, T.inv_hom_id], refl }
end

end normed_with_aut

#lint- only unused_arguments def_lemma doc_blame
