import category_theory.sites.sheaf
import category_theory.sites.sheafification

namespace category_theory.presheaf

open category_theory

universes w v u
variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w} [category.{max v u} D]

lemma is_sheaf_of_iso {F G : Cᵒᵖ ⥤ D} (η : F ≅ G) (hG : is_sheaf J G) : is_sheaf J F :=
begin
  intros T X S hS,
  let e : F ⋙ coyoneda.obj (opposite.op T) ≅ G ⋙ coyoneda.obj (opposite.op T) :=
    iso_whisker_right η _,
  apply presieve.is_sheaf_for_iso e.symm,
  apply hG _ _ hS,
end

variables [concrete_category.{max v u} D]
variables [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), limits.has_multiequalizer (S.index P)]
variables [limits.preserves_limits (forget D)]
variables [∀ (X : C), limits.has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [∀ (X : C), limits.preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
variables [reflects_isomorphisms (forget D)]

lemma _root_.category_theory.grothendieck_topology.is_iso_sheafify_lift_of_is_iso {F G : Cᵒᵖ ⥤ D}
  (η : F ⟶ G) (hG : is_sheaf J G) [h : is_iso η] : is_iso (J.sheafify_lift η hG) :=
begin
  have hF : is_sheaf J F,
  { apply is_sheaf_of_iso _ (as_iso η) hG },
  constructor,
  use inv η ≫ J.to_sheafify _,
  split,
  { apply J.sheafify_hom_ext _ _,
    { exact grothendieck_topology.plus.is_sheaf_plus_plus J F },
    simp only [← category.assoc, J.to_sheafify_sheafify_lift, is_iso.hom_inv_id,
      category.id_comp, category.comp_id] },
  { simp only [category.assoc, J.to_sheafify_sheafify_lift, is_iso.inv_hom_id] }
end

end category_theory.presheaf
