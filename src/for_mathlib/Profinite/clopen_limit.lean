import topology.category.Profinite
import topology.discrete_quotient

namespace Profinite

open category_theory
open category_theory.limits

universe u

variables {J : Type u} [semilattice_inf J] (F : J ⥤ Profinite.{u}) (C : cone F)
  (hC : is_limit C)

/-- The existence of a clopen. -/
theorem exists_clopen (U : set C.X) (hU : is_clopen U) :
  ∃ (j : J) (V : set (F.obj j)) (hV : is_clopen V), U = (C.π.app j) ⁻¹' V := sorry

/-- The images of the transition maps stabilize. -/
lemma image_stabilizes [∀ i, fintype (F.obj i)]
  (i : J) : ∃ (j : J) (hj : j ≤ i), ∀ (k : J) (hk : k ≤ j),
  set.range (F.map (hom_of_le hj)) =
  set.range (F.map (hom_of_le $ le_trans hk hj)) := sorry

/-- The images of the transition maps stabilize, in which case they agree with
the image of the cone point. -/
theorem exists_image [∀ i, fintype (F.obj i)]
  (i : J) : ∃ (j : J) (hj : j ≤ i),
  set.range (C.π.app i) = set.range (F.map $ hom_of_le $ hj) := sorry

/-- Any discrete quotient arises from some point in the limit. -/
theorem exists_discrete_quotient [∀ i, fintype (F.obj i)]
  (S : discrete_quotient C.X) : ∃ (i : J) (T : discrete_quotient (F.obj i)),
  S = T.comap (C.π.app i).continuous := sorry

end Profinite
