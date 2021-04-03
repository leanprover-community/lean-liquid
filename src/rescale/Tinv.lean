import pseudo_normed_group.Tinv
import rescale.pseudo_normed_group

open_locale classical nnreal
noncomputable theory
local attribute [instance] type_pow
open opposite ProFiltPseuNormGrpWithTinv

universe variable u
variables (r : ℝ≥0) (V : NormedGroup) [normed_with_aut r V] [fact (0 < r)]
variables (r' : ℝ≥0) [fact (0 < r')] [fact (r' ≤ 1)]
variables (M M₁ M₂ M₃ : ProFiltPseuNormGrpWithTinv.{u} r')
variables (c c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℝ≥0) (l m n : ℕ)
variables (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)

namespace CLCPTinv₂

theorem CLCFPTinv₂_rescale (r : ℝ≥0) (V : NormedGroup)
  (r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [r1 : fact (r' ≤ 1)] [normed_with_aut r V]
  (c c₂ : ℝ≥0) [fact (c₂ ≤ r' * c)] (n : ℕ)
  (N : ℝ≥0) [fact (c₂ * N⁻¹ ≤ r' * (c * N⁻¹))]
  (M) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  (CLCFPTinv₂ r V r' c c₂ n).obj (op (of r' (rescale N M))) =
  (CLCFPTinv₂ r V r' (c * N⁻¹) (c₂ * N⁻¹) n).obj (op (of r' M)) := rfl

end CLCPTinv₂

namespace breen_deligne

open CLCFPTinv

variables (M) {l m n}

namespace universal_map

variables (ϕ : universal_map m n)

theorem eval_CLCFPTinv₂_rescale
  [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [ϕ.suitable c₃ c₁] [ϕ.suitable c₄ c₂]
  (N : ℝ≥0) [fact (c₂ * N⁻¹ ≤ r' * (c₁ * N⁻¹))] [fact (c₄ * N⁻¹ ≤ r' * (c₃ * N⁻¹))]
  (M) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  (eval_CLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ ϕ).app (op (of r' (rescale N M))) ==
  (eval_CLCFPTinv₂ r V r' (c₁ * N⁻¹) (c₂ * N⁻¹) (c₃ * N⁻¹) (c₄ * N⁻¹) ϕ).app (op (of r' M)) :=
begin
  dsimp only [eval_CLCFPTinv₂, CLCFPTinv₂_def], delta id,
  apply heq_of_eq,
  dsimp only [NormedGroup.equalizer.map_nat_app],
  congr' 1,
end

end universal_map
end breen_deligne
