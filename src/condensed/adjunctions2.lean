import condensed.adjunctions
import condensed.top_comparison

noncomputable theory

universe u

open category_theory

namespace condensed

def profinite_free_adj (M : Condensed.{u} Ab.{u+1}) :
  (Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab).op ⋙ preadditive_yoneda.obj M ≅
  M.val :=
sorry

end condensed
