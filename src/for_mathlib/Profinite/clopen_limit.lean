import topology.category.Profinite
import topology.discrete_quotient
import for_mathlib.Top

noncomputable theory

namespace Profinite

open category_theory
open category_theory.limits

universe u

variables {J : Type u} [semilattice_inf J] (F : J ⥤ Profinite.{u}) (C : cone F)

def created_cone : limits.cone F :=
  lift_limit (Top.limit_cone_Inf_is_limit $ F ⋙ Profinite_to_Top)

def created_cone_is_limit : limits.is_limit (created_cone F) :=
  lifted_limit_is_limit _

def cone_iso (hC : is_limit C) : C ≅ (created_cone F) :=
hC.unique_up_to_iso $ created_cone_is_limit _

def cone_point_iso (hC : is_limit C) : C.X ≅ (created_cone F).X :=
(cones.forget _).map_iso $ cone_iso _ _ hC

def created_iso : Profinite_to_Top.map_cone (created_cone F) ≅
  (Top.limit_cone_Inf $ F ⋙ Profinite_to_Top) :=
lifted_limit_maps_to_original _

def created_point_iso : Profinite_to_Top.obj (created_cone F).X ≅
  (Top.limit_cone_Inf $ F ⋙ Profinite_to_Top).X := (cones.forget _).map_iso $
created_iso _

def iso_to_Top (hC : is_limit C) : Profinite_to_Top.obj C.X ≅
  (Top.limit_cone_Inf $ F ⋙ Profinite_to_Top).X :=
  Profinite_to_Top.map_iso (cone_point_iso _ _ hC) ≪≫ created_point_iso _

def cone_homeo (hC : is_limit C) :
  C.X ≃ₜ (Top.limit_cone_Inf $ F ⋙ Profinite_to_Top).X :=
let FF := iso_to_Top _ _ hC in
{ to_fun := FF.hom,
  inv_fun := FF.inv,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  continuous_to_fun := FF.hom.continuous,
  continuous_inv_fun := FF.inv.continuous }

lemma exists_clopen' [inhabited J]
  (U : set (Top.limit_cone_Inf $ F ⋙ Profinite_to_Top).X) (hU : is_clopen U) :
  ∃ (j : J) (V : set (F.obj j)) (hV : is_clopen V),
  U = ((Top.limit_cone_Inf $ F ⋙ Profinite_to_Top).π.app j) ⁻¹' V :=
begin
  cases hU with h1 hU,
  sorry,
end

/-- The existence of a clopen. -/
theorem exists_clopen [inhabited J]
  (hC : is_limit C) (U : set C.X) (hU : is_clopen U) :
  ∃ (j : J) (V : set (F.obj j)) (hV : is_clopen V), U = (C.π.app j) ⁻¹' V :=
begin
  let FF := cone_homeo _ _ hC,
  let UU := FF.symm ⁻¹' U,
  have hUU : is_clopen UU,
  { split,
    exact is_open.preimage (FF.symm.continuous) hU.1,
    exact is_closed.preimage (FF.symm.continuous) hU.2 },
  rcases exists_clopen' F UU hUU with ⟨j,V,hV,hJ⟩,
  use j, use V, use hV,
  dsimp only [UU] at hJ,
  have : U = FF ⁻¹' (((Top.limit_cone_Inf (F ⋙ Profinite_to_Top)).π.app j) ⁻¹' V),
  { rw [← hJ, ← set.preimage_comp],
    simp },
  rw this,
  rw ← set.preimage_comp,
  congr' 1,
  have : C.π.app j = (cone_point_iso _ _ hC).hom ≫ (created_cone _).π.app j,
  { have := (cone_iso _ _ hC).hom.w,
    rw ← this,
    refl },
  rw this,
  refl,
end

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
