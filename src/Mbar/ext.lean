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

def condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
Mbar.functor.{u u} r' ⋙ to_PFPNG₁.{u} _ ⋙ to_CHFPNG₁.{u} ⋙ to_Condensed.{u}

/-
WARNING/TODO:: We need the `ℤ[T⁻¹]`-linear version of the following statement,
instead of the `Ab`-version.
-/

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem Ext_iso_zero (S : Profinite.{0}) (V : SemiNormedGroup.{0}) [normed_with_aut r V] (i : ℕ) :
  ((Ext ℤ (Condensed.{0} Ab.{1}) i).obj
    (op $ (condensed.{0} r').obj S)).obj
      (Condensed.of_top_ab V) ≅ 0 :=
sorry

end Mbar
