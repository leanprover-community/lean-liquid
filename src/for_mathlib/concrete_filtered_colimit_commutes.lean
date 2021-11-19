import category_theory.limits.concrete_category
import category_theory.limits.filtered_colimit_commutes_finite_limit

namespace category_theory

namespace limits

universes v u w

variables {J K : Type v} [small_category J] [small_category K]
variables {D : Type w} [category.{v} D]
variables [concrete_category.{v} D]
variables [preserves_colimits_of_shape K (forget D)]
variables [preserves_limits_of_shape J (forget D)]
variables [has_colimits_of_shape K D]
variables [has_limits_of_shape J D]
variables [reflects_isomorphisms (forget D)]

variables (F : J × K ⥤ D)

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

noncomputable
def limit_forget_iso_forget_limit : (curry.obj (prod.swap K J ⋙ F) ⋙ lim) ⋙ forget D ≅
  (curry.obj (prod.swap K J ⋙ (F ⋙ forget D)) ⋙ lim) :=
nat_iso.of_components (λ k, (is_limit_of_preserves (forget D)
  (limit.is_limit _)).cone_point_unique_up_to_iso (limit.is_limit _))
begin
  intros i j f,
  ext1 t,
  have := ((is_limit_of_preserves (forget D)
   (limit.is_limit ((curry.obj (prod.swap K J ⋙ F)).obj j))).unique_up_to_iso
   (limit.is_limit ((curry.obj (prod.swap K J ⋙ F)).obj j ⋙ forget D))).hom.w t,
  dsimp [is_limit.cone_point_unique_up_to_iso, cones.forget, functor.map_iso],
  dsimp at this,
  simp only [forget_map_eq_coe, limit.lift_π, cones.postcompose_obj_π,
    functor.comp_map, functor.map_cone_π_app, curry.obj_map_app, prod.swap_map,
    limit.cone_π, limit.lift_map, nat_trans.comp_app, category.assoc],
  erw [this, ← (forget D).map_comp, ← (forget D).map_comp],
  congr' 1,
  simp,
end

noncomputable
def forget_colimit_limit_iso :
  (forget D).obj (colimit (curry.obj (prod.swap K J ⋙ F) ⋙ lim)) ≅
    colimit (curry.obj (prod.swap K J ⋙ F ⋙ forget D) ⋙ lim) :=
(is_colimit_of_preserves (forget D) (colimit.is_colimit _)).cocone_point_unique_up_to_iso
  (colimit.is_colimit _) ≪≫ has_colimit.iso_of_nat_iso (limit_forget_iso_forget_limit F)

noncomputable
def colimit_forget_iso_forget_colimit : (curry.obj F ⋙ colim) ⋙ forget D ≅
  (curry.obj (F ⋙ forget D) ⋙ colim) :=
nat_iso.of_components _ _

noncomputable
def forget_limit_colimit_iso :
  (forget D).obj (limit (curry.obj F ⋙ colim)) ≅
    limit (curry.obj (F ⋙ forget D) ⋙ colim) :=
(is_limit_of_preserves (forget D) (limit.is_limit _)).cone_point_unique_up_to_iso
  (limit.is_limit _) ≪≫ has_limit.iso_of_nat_iso (colimit_forget_iso_forget_colimit F)

lemma forget_colimit_limit_to_limit_colimit_eq :
  (forget D).map (colimit_limit_to_limit_colimit F) =
  (forget_colimit_limit_iso F).hom ≫ colimit_limit_to_limit_colimit (F ⋙ forget D) ≫
  (forget_limit_colimit_iso F).inv := sorry

instance [is_filtered K] [fin_category J] :
  is_iso (colimit_limit_to_limit_colimit F) :=
begin
  suffices : (is_iso ((forget D).map (colimit_limit_to_limit_colimit F))),
  { apply is_iso_of_reflects_iso _ (forget D), exact this },
  rw forget_colimit_limit_to_limit_colimit_eq,
  suffices : is_iso ((colimit_limit_to_limit_colimit (F ⋙ forget D))),
  { resetI, apply is_iso.comp_is_iso },
  apply category_theory.limits.colimit_limit_to_limit_colimit_is_iso,
end

end limits

end category_theory
