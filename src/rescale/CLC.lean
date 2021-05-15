import pseudo_normed_group.CLC
import rescale.LC

open_locale classical nnreal
open opposite ProFiltPseuNormGrpWithTinv

open SemiNormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group

universe variable u
variables (r : ℝ≥0) (V : SemiNormedGroup) (r' : ℝ≥0) [fact (0 < r')]
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (m n : ℕ)

@[simp] theorem CLCFP_rescale (N : ℝ≥0)
  (M) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  (CLCFP V r' c n).obj (op (of r' (rescale N M))) =
  (CLCFP V r' (c * N⁻¹) n).obj (op (of r' M)) := rfl

namespace breen_deligne

namespace universal_map

variables (ϕ : universal_map m n)

theorem eval_CLCFP_rescale [ϕ.suitable c₂ c₁]
  (N : ℝ≥0)
  (M : ProFiltPseuNormGrpWithTinv r') :
  arrow.mk ((eval_CLCFP V r' c₁ c₂ ϕ).app (op (of r' (rescale N M)))) =
  arrow.mk ((eval_CLCFP V r' (c₁ * N⁻¹) (c₂ * N⁻¹) ϕ).app (op M)) :=
by { dsimp only [eval_CLCFP, whisker_right_app], rw eval_LCFP_rescale, cases M, refl }

end universal_map

end breen_deligne
