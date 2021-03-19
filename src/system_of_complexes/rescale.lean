import system_of_complexes.basic
import normed_group.rescale

noncomputable theory

namespace system_of_complexes

open category_theory
open_locale nat

def rescale_functor (m : ℕ) : system_of_complexes ⥤ system_of_complexes :=
(whiskering_right _ _ _).obj $ functor.map_complex_like $ NormedGroup.rescale_functor m

def rescale_nat_trans (i j : ℕ) : rescale_functor i ⟶ rescale_functor j :=
(whiskering_right _ _ _).map $ functor.map_complex_like_nat_trans _ _ $
  NormedGroup.rescale_nat_trans i j

instance rescale_functor.additive (m : ℕ) : (rescale_functor m).additive :=
sorry

end system_of_complexes
