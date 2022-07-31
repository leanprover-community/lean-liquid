import examples.Radon.basic

open_locale nnreal classical
noncomputable theory

namespace Profinite

-- Key calculation 1
def real_measures_iso (p c : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  real_measures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c ⋙ CompHaus_to_Top ≅
  Fintype.to_Profinite ⋙ Radon_functor p c := sorry

end Profinite
