import laurent_measures.functor
import condensed.ab

noncomputable theory

universe u

open category_theory

open_locale nnreal

namespace laurent_measures

def condensed (r' : ℝ≥0) [fact (0 < r')] : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
(laurent_measures.profinite.{u} r' ⋙
  PFPNGT₁_to_CHFPNG₁ₗₑ.{u} r') ⋙
  CompHausFiltPseuNormGrp₁.to_Condensed

def condensedCH (r' : ℝ≥0) [fact (0 < r')] : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
laurent_measures.profiniteCH.{u} r' ⋙ CompHausFiltPseuNormGrp₁.to_Condensed

end laurent_measures
