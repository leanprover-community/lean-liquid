import category_theory.sites.limits

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits

universes w v u

variables {C : Type (max v u)} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w} [category.{max v u} D]
-- We need to sheafify
variables [concrete_category.{max v u} D]
variables [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
variables [preserves_limits (forget D)]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
variables [reflects_isomorphisms (forget D)]

noncomputable theory

instance plus_functor_preserves_finite_limits (K : Type (max v u))
  [small_category K] [fin_category K] :
  preserves_limits_of_shape K (J.plus_functor D) := sorry

instance sheafification_preserves_finite_limits (K : Type (max v u))
  [small_category K] [fin_category K] :
  preserves_limits_of_shape K (sheafification J D) :=
by { delta sheafification, apply_instance }

instance presheaf_to_Sheaf_preserves_finite_limits (K : Type (max v u))
  [small_category K] [fin_category K] [has_limits_of_shape K D] :
  preserves_limits_of_shape K (presheaf_to_Sheaf J D) :=
begin
  constructor, intros F, constructor, intros E hE,
  suffices h : is_limit ((Sheaf_to_presheaf J D).map_cone ((presheaf_to_Sheaf J D).map_cone E)),
  { let e := lifted_limit_is_limit h,
    let ee : lift_limit h ≅ (presheaf_to_Sheaf J D).map_cone E,
    { let d := lifted_limit_maps_to_original h,
      let dd := (cones.forget _).map_iso d,
      fapply cones.ext,
      { exact ⟨dd.hom, dd.inv, dd.hom_inv_id, dd.inv_hom_id⟩ },
      { intros j, exact (d.hom.w j).symm } },
    apply is_limit.of_iso_limit e ee },
  apply is_limit_of_preserves (sheafification J D) hE,
end

end category_theory.grothendieck_topology
