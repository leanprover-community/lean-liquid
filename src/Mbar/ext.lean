import category_theory.abelian.ext

import liquid
import Mbar.functor
import condensed.projective_resolution

noncomputable theory

universe u

open opposite category_theory
open_locale nnreal

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]

namespace Mbar

open ProFiltPseuNormGrpWithTinv₁ ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁

def condensed : Profinite ⥤ Condensed Ab.{u+1} :=
Mbar.functor.{u+1 u+1} r' ⋙ to_PFPNG₁.{u+1} _ ⋙ to_CHFPNG₁.{u+1} ⋙ to_Condensed.{u}

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem Ext_iso_zero (S : Profinite) (V : SemiNormedGroup) [normed_with_aut r V] (i : ℕ) :
  ((Ext ℤ (Condensed Ab.{1}) i).obj
    (op $ (condensed.{0} r').obj S)).obj
      (Condensed.of_top_ab V) ≅ 0 :=
sorry

end Mbar
