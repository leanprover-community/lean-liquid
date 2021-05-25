import topology.category.Profinite
import topology.discrete_quotient

noncomputable theory

namespace Profinite

open category_theory
open category_theory.limits

universe u

variables {J : Type u} [semilattice_inf J] (F : J ⥤ Profinite.{u}) (C : cone F)

def created_cone : limits.cone F :=
  lift_limit (Top.limit_cone_is_limit $ F ⋙ Profinite_to_Top)

def created_cone_is_limit : limits.is_limit (created_cone F) :=
  lifted_limit_is_limit _

def cone_iso (hC : is_limit C) : C.X ≅ (created_cone F).X :=
hC.cone_point_unique_up_to_iso $ created_cone_is_limit _

def cone_iso_Top (hC : is_limit C) :
  Profinite_to_Top.obj C.X ≅ (Top.limit_cone $ F ⋙ Profinite_to_Top).X :=
let A := lifted_limit_maps_to_original (Top.limit_cone_is_limit $ F ⋙ Profinite_to_Top) in
Profinite_to_Top.map_iso (cone_iso _ _ hC) ≪≫ (cones.forget _).map_iso A

/-- The existence of a clopen. -/
theorem exists_clopen (hC : is_limit C) (U : set C.X) (hU : is_clopen U) :
  ∃ (j : J) (V : set (F.obj j)) (hV : is_clopen V), U = (C.π.app j) ⁻¹' V := sorry

/-- The images of the transition maps stabilize. -/
lemma image_stabilizes [∀ i, fintype (F.obj i)]
  (i : J) : ∃ (j : J) (hj : j ≤ i), ∀ (k : J) (hk : k ≤ j),
  set.range (F.map (hom_of_le hj)) =
  set.range (F.map (hom_of_le $ le_trans hk hj)) := sorry

/-- The images of the transition maps stabilize, in which case they agree with
the image of the cone point. -/
theorem exists_image [∀ i, fintype (F.obj i)] (hC : is_limit C)
  (i : J) : ∃ (j : J) (hj : j ≤ i),
  set.range (C.π.app i) = set.range (F.map $ hom_of_le $ hj) := sorry

/-- Any discrete quotient arises from some point in the limit. -/
theorem exists_discrete_quotient [∀ i, fintype (F.obj i)] (hC : is_limit C)
  (S : discrete_quotient C.X) : ∃ (i : J) (T : discrete_quotient (F.obj i)),
  S = T.comap (C.π.app i).continuous := sorry

end Profinite
