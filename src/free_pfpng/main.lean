import free_pfpng.basic
import condensed.projective_resolution

/-- Prop 2.1 of Analytic.pdf -/
def free_pfpng_profinite_iso :
  free_pfpng_profinite ⋙
  ProFiltPseuNormGrp₁.enlarging_functor ⋙
  ProFiltPseuNormGrp.to_CompHausFilt ⋙
  CompHausFiltPseuNormGrp.to_Condensed ≅
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab := sorry
