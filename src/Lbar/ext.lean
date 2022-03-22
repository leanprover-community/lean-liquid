import for_mathlib.derived.K_projective
import liquid
import Lbar.functor
import condensed.projective_resolution

noncomputable theory

universe u

open opposite category_theory
open_locale nnreal

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]

namespace Lbar

open ProFiltPseuNormGrpWithTinv₁ ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁

def condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
(Lbar.functor.{u u} r' ⋙ to_PFPNG₁.{u} _) ⋙ (to_CHFPNG₁.{u} ⋙ to_Condensed.{u})

-- def Tinv : Lbar.condensed.{u} r' ⟶ Lbar.condensed.{u} r' :=
-- whisker_right
--   (whisker_left (Lbar.functor.{u u} r') $
--   { app := λ M, @profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv r' M _,
--     naturality' := _ })
--   (to_CHFPNG₁.{u} ⋙ to_Condensed.{u})




/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem Ext_iso_zero (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] (i : ℤ) :
  ((Ext' i).obj
    (op $ (Lbar.condensed.{u} r').obj S)).obj
      (Condensed.of_top_ab V) ≅ 0 :=
-- TODO/WARNING: this statement needs to be updated
-- see https://leanprover-community.github.io/liquid/sect0010.html#Ext-Lbar
sorry

end Lbar
