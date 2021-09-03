import category_theory.abelian.projective

import condensed.condensed

/-!
# Properties of the category of condensed abelian groups

-/

open category_theory category_theory.limits

universes v u

namespace Condensed

instance : preadditive (Condensed Ab.{u+1}) := sorry

instance : abelian (Condensed Ab.{u+1}) := sorry

instance : enough_projectives (Condensed Ab.{u+1}) := sorry

end Condensed
