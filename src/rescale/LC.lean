import rescale.pseudo_normed_group
import pseudo_normed_group.LC

open_locale classical nnreal
open opposite ProFiltPseuNormGrpWithTinv

open NormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group

universe variable u
variables (r : ℝ≥0) (V : NormedGroup) (r' : ℝ≥0) [fact (0 < r')]
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)

@[simp] theorem LCFP_rescale (N : ℝ≥0)
  (M) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  (LCFP V r' c n).obj (op (of r' (rescale N M))) =
  (LCFP V r' (c * N⁻¹) n).obj (op (of r' M)) := rfl

namespace breen_deligne

namespace basic_universal_map

variables (ϕ : basic_universal_map m n)

-- theorem eval_FP_rescale [ϕ.suitable c₁ c₂]
--   (N : ℝ≥0)
--   (M) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
--   (eval_FP r' c₁ c₂ ϕ).app (of r' (rescale N M)) =
--   ((eval_FP r' (c₁ * N⁻¹) (c₂ * N⁻¹) ϕ).app (of r' M)) := rfl

theorem eval_LCFP_rescale [ϕ.suitable c₂ c₁]
  (N : ℝ≥0) (M) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  (eval_LCFP V r' ϕ c₁ c₂).app (op (of r' (rescale N M))) =
  by clean @_root_.id _ ((eval_LCFP V r' ϕ (c₁ * N⁻¹) (c₂ * N⁻¹)).app (op (of r' M))) :=
begin
  sorry
end

end basic_universal_map

namespace universal_map

variables (ϕ : universal_map m n)

theorem eval_LCFP_rescale [ϕ.suitable c₂ c₁]
  (N : ℝ≥0)
  (M) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  (eval_LCFP V r' c₁ c₂ ϕ).app (op (of r' (rescale N M))) =
  (by clean @_root_.id _ ((eval_LCFP V r' (c₁ * N⁻¹) (c₂ * N⁻¹) ϕ).app (op (of r' M)))) :=
begin
  simp only [eval_LCFP, ← nat_trans.app_hom_apply,
    add_monoid_hom.map_sum, add_monoid_hom.map_int_module_smul],
  simp only [nat_trans.app_hom_apply, basic_universal_map.eval_LCFP_rescale],
end

end universal_map

end breen_deligne
