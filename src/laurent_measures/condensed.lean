import laurent_measures.functor
import condensed.ab

noncomputable theory

universe u

open category_theory

open_locale nnreal

namespace laurent_measures

def condensed (r' : ℝ≥0) [fact (0 < r')] : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
laurent_measures.functor.{u u} r' ⋙ CompHausFiltPseuNormGrp₁.to_Condensed

end laurent_measures
