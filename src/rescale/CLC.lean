import rescale.LC
import pseudo_normed_group.CLC

open_locale classical nnreal
open opposite ProFiltPseuNormGrpWithTinv

open NormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group

universe variable u
variables (r : ℝ≥0) (V : NormedGroup) (r' : ℝ≥0) [fact (0 < r')]
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)

@[simp] theorem CLCFP_rescale (N : ℝ≥0)
  (M) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  (CLCFP V r' c n).obj (op (of r' (rescale N M))) =
  (CLCFP V r' (c * N⁻¹) n).obj (op (of r' M)) := rfl

namespace breen_deligne

namespace universal_map

variables (ϕ : universal_map m n)

theorem eval_CLCFP_rescale [ϕ.suitable c₂ c₁]
  (N : ℝ≥0)
  (M) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  (eval_CLCFP V r' c₁ c₂ ϕ).app (op (of r' (rescale N M))) ==
  (eval_CLCFP V r' (c₁ * N⁻¹) (c₂ * N⁻¹) ϕ).app (op (of r' M)) :=
by { dsimp [eval_CLCFP], rw eval_LCFP_rescale }

end universal_map

end breen_deligne
