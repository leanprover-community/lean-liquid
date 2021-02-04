import for_mathlib.equalizers
import for_mathlib.extend_from_nat

import system_of_complexes
import pseudo_normed_group.CLC
import pseudo_normed_group.category

open_locale classical nnreal
noncomputable theory
local attribute [instance] type_pow

open NormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group

universe variable u
variables (V : NormedGroup)
variables {r' : ℝ≥0} {M M₁ M₂ M₃ : Type u}
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₁]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₂]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₃]
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (m n : ℕ) (ϕ : basic_universal_map m n)
variables (f : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂)
variables (g : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₂ M₃)

-- -- give a better name
-- def preobject (r' : ℝ≥0) (V : NormedGroup) (n : ℕ) :
--   (ProFiltPseuNormGrpWithTinv r') × ℝ≥0ᵒᵖ ⥤ NormedGroup :=
-- { obj := λ Mc, (op $ of ((filtration Mc.1 (unop Mc.2) : Type*)^n)),
--   map := λ Mc Nd f, _,
--   map_id' := _,
--   map_comp' := _ } ⋙ (LocallyConstant.obj V)

namespace breen_deligne
namespace package

variables (BD : breen_deligne.package) (c' : ℕ → ℝ≥0) [BD.suitable c']

open NormedGroup opposite Profinite pseudo_normed_group category_theory

-- /-- The complex of (uncompleted) normed groups `V(M_{≤c}) ⟶ V(M_{≤c_1c}^2) ⟶ …` -/
-- def precomplex (V : NormedGroup) (M : Type*) (c : ℝ≥0) [profinitely_filtered_pseudo_normed_group M] :
--   cochain_complex NormedGroup :=
-- { /- the objects -/
--   X := int.extend_from_nat 0 $ λ i,
--     (LocallyConstant.obj V).obj (op $ of ((filtration M (c * c' i) : Type*)^(BD.rank i))),
--   /- the differentials -/
--   d := int.extend_from_nat 0 $ λ i,
--     (LocallyConstant.obj V).map (has_hom.hom.op $ ⟨(BD.map i).eval_png₀ _ _ _, _⟩),
--   -- (BD.map i).eval_Mbar_pow_Tinv V S r r' (c * c' (i+1)) (c * c' i),
--   d_squared' := /- d^2 = 0 -/
--   begin
--     ext1 ⟨i⟩,
--     { dsimp,
--       simp only [pi.comp_apply, pi.zero_apply],
--       erw ← universal_map.eval_Mbar_pow_Tinv_comp V S r r' _ (c * c' (i+1)) _ (BD.map i) (BD.map (i+1)),
--       simp only [BD.map_comp_map, universal_map.eval_Mbar_pow_Tinv_zero],
--       apply_instance },
--     { show 0 ≫ _ = 0, rw [zero_comp] }
--   end }

end package
end breen_deligne
