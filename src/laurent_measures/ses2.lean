import laurent_measures.ses
import laurent_measures.condensed
import real_measures.condensed
import condensed.exact

universe u

noncomputable theory

open category_theory

open_locale nnreal

namespace laurent_measures

variables (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)]

local notation `r` := @r p

def Θ_condensed (S : Profinite.{u}) :
  (condensed r).obj S ⟶ (real_measures.condensed p).obj S :=
sorry

end laurent_measures
