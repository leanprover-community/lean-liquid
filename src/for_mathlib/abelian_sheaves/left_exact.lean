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

instance {K : Type (max v u)} [small_category K] [fin_category K] :
  preserves_limits_of_shape K (J.plus_functor D) := sorry

noncomputable
instance preserves_limit_of_shape_presheaf_to_Sheaf {K : Type (max v u)} [small_category K]
  [fin_category K] [has_limits_of_shape K D] :
  preserves_limits_of_shape K (presheaf_to_Sheaf J D) :=
begin
  -- This can probably be simplified...
  constructor,
  dsimp,
  intros F,
  constructor,
  intros E hE,
  suffices h : is_limit ((Sheaf_to_presheaf J D).map_cone ((presheaf_to_Sheaf J D).map_cone E)),
  { let e := lifted_limit_is_limit h,
    have ee : lift_limit h ≅ (presheaf_to_Sheaf J D).map_cone E,
    { let d := lifted_limit_maps_to_original h,
      let dd := (cones.forget _).map_iso d,
      fapply cones.ext,
      { refine ⟨dd.hom, dd.inv, dd.hom_inv_id, dd.inv_hom_id⟩ },
      intros j,
      have := d.hom.w j,
      exact this.symm },
    apply is_limit.of_iso_limit e ee },
  have h : (Sheaf_to_presheaf J D).map_cone ((presheaf_to_Sheaf J D).map_cone E)
    ≅ (sheafification J D).map_cone E := eq_to_iso rfl,
  suffices : is_limit ((sheafification J D).map_cone E),
  { apply is_limit.of_iso_limit this h },
  clear h,
  have h : (sheafification J D).map_cone E ≅
    (J.plus_functor D).map_cone ((J.plus_functor D).map_cone E) := eq_to_iso rfl,
  suffices : is_limit ((J.plus_functor D).map_cone ((J.plus_functor D).map_cone E)),
  { apply is_limit.of_iso_limit this h },
  apply is_limit_of_preserves,
  apply is_limit_of_preserves,
  exact hE,
end

end category_theory.grothendieck_topology
