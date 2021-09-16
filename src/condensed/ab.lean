import category_theory.abelian.projective
import pseudo_normed_group.category

import condensed.basic

/-!
# Properties of the category of condensed abelian groups

-/

open category_theory category_theory.limits

universes v u

namespace Condensed

instance : preadditive (Condensed Ab.{u+1}) := sorry

instance : abelian (Condensed Ab.{u+1}) := sorry

instance : enough_projectives (Condensed Ab.{u+1}) := sorry

def CompHausFiltPseuNormGrp.to_Condensed :
  CompHausFiltPseuNormGrp ⥤ Condensed Ab :=
sorry

end Condensed
