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
def colimit_forget_iso_forget_colimit :
  (curry.obj (F ⋙ forget D) ⋙ colim) ≅ (curry.obj F ⋙ colim) ⋙ forget D :=
nat_iso.of_components (λ X,
  (colimit.is_colimit ((curry.obj F).obj X ⋙ forget D)).cocone_point_unique_up_to_iso
  (is_colimit_of_preserves (forget D) (colimit.is_colimit _)))
begin
  intros x y f,
  ext1 k,
  have := ((is_colimit_of_preserves (forget D) (colimit.is_colimit
    ((curry.obj F).obj y))).unique_up_to_iso
    (colimit.is_colimit ((curry.obj F).obj y ⋙ forget D))).inv.w k,
  dsimp [is_colimit.cocone_point_unique_up_to_iso, functor.map_cocone, cocones.functoriality],
  dsimp at this,
  simp,
  erw [this, colimit.ι_desc_assoc],
  dsimp,
  erw [← (forget D).map_comp, ← (forget D).map_comp],
  congr' 1,
  simp,
end

noncomputable
def forget_limit_colimit_iso :
  (forget D).obj (limit (curry.obj F ⋙ colim)) ≅
    limit (curry.obj (F ⋙ forget D) ⋙ colim) :=
(is_limit_of_preserves (forget D) (limit.is_limit _)).cone_point_unique_up_to_iso
  (limit.is_limit _) ≪≫ has_limit.iso_of_nat_iso (colimit_forget_iso_forget_colimit F).symm

lemma forget_colimit_limit_to_limit_colimit_eq :
  (forget D).map (colimit_limit_to_limit_colimit F) =
  (forget_colimit_limit_iso F).hom ≫ colimit_limit_to_limit_colimit (F ⋙ forget D) ≫
  (forget_limit_colimit_iso F).inv :=
begin
  rw ← iso.inv_comp_eq,
  rw iso.eq_comp_inv,
  ext k j : 2,
  dsimp [forget_colimit_limit_iso, forget_limit_colimit_iso,
    is_colimit.cocone_point_unique_up_to_iso, is_limit.cone_point_unique_up_to_iso],
  simp only [category.assoc, colimit.ι_desc_assoc, colimit.ι_desc,
    limit.lift_π, limit.lift_π_assoc, ι_colimit_limit_to_limit_colimit_π,
    has_limit.iso_of_nat_iso_hom_π],
  dsimp [functor.map_cone],
  dsimp [has_colimit.iso_of_nat_iso, is_colimit.map],
  rw colimit.ι_desc_assoc,
  dsimp [cocones.precompose, limit_forget_iso_forget_limit, nat_iso.of_components,
    is_limit.cone_point_unique_up_to_iso, colimit_forget_iso_forget_colimit,
    is_colimit.cocone_point_unique_up_to_iso],
  simp only [category.assoc, colimit.ι_desc_assoc],
  dsimp [functor.map_cocone],
  slice_lhs 2 4 { erw [← (forget D).map_comp, ← (forget D).map_comp,
    ι_colimit_limit_to_limit_colimit_π] },
  rw [(forget D).map_comp, category.assoc],
  have := (is_colimit_of_preserves (forget D) (colimit.is_colimit ((curry.obj F).obj j))).fac
    (colimit.cocone _) k,
  erw [this, ← category.assoc], clear this,
  have := (is_limit_of_preserves (forget D)
    (limit.is_limit ((curry.obj (prod.swap K J ⋙ F)).obj k))).fac (limit.cone _) j,
  erw [this], clear this,
  refl,
end

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

@[simps]
noncomputable
def flip_lim_iso_curry_swap_uncurry_lim (F : J ⥤ K ⥤ D) :
  F.flip ⋙ lim ≅ curry.obj (prod.swap K J ⋙ uncurry.obj F) ⋙ lim :=
nat_iso.of_components (λ k, has_limit.iso_of_nat_iso $
  nat_iso.of_components (λ t, eq_to_iso rfl) $ λ i j f, by { dsimp, simp }) $ λ i j f,
      by { ext, dsimp, simp, dsimp, simp }

@[simps]
noncomputable
def colim_iso_curry_uncurry_colim (F : J ⥤ K ⥤ D) :
  F ⋙ colim ≅ curry.obj (uncurry.obj F) ⋙ colim :=
nat_iso.of_components (λ k, has_colimit.iso_of_nat_iso $
  nat_iso.of_components (λ t, eq_to_iso rfl) $ λ i j f, by { dsimp, simp }) $ λ i j f,
    by { ext, dsimp, simp }

noncomputable
def curried_colimit_limit_to_limit_colimit (F : J ⥤ K ⥤ D) :
  colimit (F.flip ⋙ lim) ⟶ limit (F ⋙ colim) :=
(has_colimit.iso_of_nat_iso (flip_lim_iso_curry_swap_uncurry_lim.{v} F)).hom ≫
colimit_limit_to_limit_colimit (uncurry.obj F) ≫
(has_limit.iso_of_nat_iso (colim_iso_curry_uncurry_colim.{v} F)).inv

@[simp, reassoc]
lemma ι_curried_colimit_limit_to_limit_colimit_π (F : J ⥤ K ⥤ D) (k) (j) :
  colimit.ι (F.flip ⋙ lim) k ≫ curried_colimit_limit_to_limit_colimit F ≫
  limit.π (F ⋙ colim) j = limit.π _ j ≫ colimit.ι (F.obj j) k :=
begin
  delta curried_colimit_limit_to_limit_colimit,
  dsimp [has_colimit.iso_of_nat_iso, has_limit.iso_of_nat_iso,
    is_colimit.map, is_limit.map],
  simp only [ι_colimit_limit_to_limit_colimit_π_assoc,
    flip_lim_iso_curry_swap_uncurry_lim_hom_app, limit.lift_π,
    cones.postcompose_obj_π, has_limit.iso_of_nat_iso_hom_π_assoc,
    colimit.ι_desc_assoc, limit.cone_π, colimit.cocone_ι, nat_iso.of_components.hom_app,
    cocones.precompose_obj_ι, nat_trans.comp_app, category.assoc,
    colim_iso_curry_uncurry_colim_inv_app],
  rw [← category.assoc, ← category.assoc, iso.comp_inv_eq],
  dsimp [has_colimit.iso_of_nat_iso, has_limit.iso_of_nat_iso,
    is_colimit.map, is_limit.map],
  simp,
end

instance [is_filtered K] [fin_category J] (F : J ⥤ K ⥤ D) :
  is_iso (curried_colimit_limit_to_limit_colimit F) :=
begin
  delta curried_colimit_limit_to_limit_colimit,
  apply_instance
end

@[simps]
noncomputable def flip_lim_cone (F : J ⥤ K ⥤ D) :
  cone F :=
{ X := F.flip ⋙ lim,
  π :=
  { app := λ i, { app := λ k, limit.π _ _ },
    naturality' := begin
      intros i j f,
      ext,
      have := limit.w (F.flip.obj x) f,
      dsimp at *,
      simp [this],
    end } }

@[simps]
noncomputable def is_limit_flip_lim_cone (F : J ⥤ K ⥤ D) :
  is_limit (flip_lim_cone F) :=
evaluation_jointly_reflects_limits _ (λ k,
  is_limit.of_iso_limit (limit.is_limit (F.flip.obj k))
    (cones.ext (has_limit.iso_of_nat_iso $ nat_iso.of_components
      (λ j, eq_to_iso rfl) (by tidy)) (by tidy)))

@[simps]
noncomputable
def flip_lim_iso_limit (F : J ⥤ K ⥤ D) :
  F.flip ⋙ lim ≅ limit F :=
(is_limit_flip_lim_cone F).cone_point_unique_up_to_iso (limit.is_limit _)

@[simps]
noncomputable def colim_cocone (F : J ⥤ K ⥤ D) :
  cocone F.flip :=
{ X := F ⋙ colim,
  ι :=
  { app := λ i, { app := λ k, colimit.ι _ i },
  naturality' := λ i j f, by { ext, dsimp, simp } } }

@[simps]
noncomputable
def is_colimit_colim_cocone (F : J ⥤ K ⥤ D) :
  is_colimit (colim_cocone F) :=
evaluation_jointly_reflects_colimits _ $ λ j,
  is_colimit.of_iso_colimit (colimit.is_colimit _)
  (cocones.ext (has_colimit.iso_of_nat_iso $ nat_iso.of_components
    (λ k, eq_to_iso rfl) (by tidy)) (by tidy))

@[simps]
noncomputable
def colim_iso_colimit (F : J ⥤ K ⥤ D) :
  F ⋙ colim ≅ colimit F.flip :=
(is_colimit_colim_cocone F).cocone_point_unique_up_to_iso (colimit.is_colimit _)

noncomputable
def colimit_limit_to_limit_colimit' (F : J ⥤ K ⥤ D) :
  colimit (limit F) ⟶ limit (colimit F.flip) :=
(has_colimit.iso_of_nat_iso (flip_lim_iso_limit.{v} F)).inv ≫
curried_colimit_limit_to_limit_colimit F ≫
(has_limit.iso_of_nat_iso (colim_iso_colimit.{v} F)).hom

@[simp]
lemma ι_colimit_limit_to_limit_colimit'_π (F : J ⥤ K ⥤ D) (k) (j) :
  colimit.ι (limit F) k ≫ colimit_limit_to_limit_colimit' F ≫
  limit.π (colimit F.flip) j = (limit.π F j).app k ≫ (colimit.ι F.flip k).app j :=
begin
  dsimp only [colimit_limit_to_limit_colimit',
    has_colimit.iso_of_nat_iso, has_limit.iso_of_nat_iso,
    is_colimit.map, is_limit.map, is_colimit.cocone_points_iso_of_nat_iso,
    is_limit.cone_points_iso_of_nat_iso],
  simp only [category.assoc],
  erw limit.lift_π,
  erw colimit.ι_desc_assoc,
  dsimp only [cocones.precompose, cones.postcompose,
    nat_trans.comp_app],
  simp only [category.assoc],
  erw ι_curried_colimit_limit_to_limit_colimit_π_assoc F,
  dsimp [nat_iso.of_components, has_limit.iso_of_nat_iso, has_colimit.iso_of_nat_iso,
    is_limit.map, is_colimit.map],
  simp only [cones.postcompose_obj_π, colimit.ι_desc_assoc, limit.cone_π, limit.lift_π_assoc,
    whisker_right_app, colimit.cocone_ι, colimit.ι_desc, evaluation_obj_map, category.id_comp,
    cocones.precompose_obj_ι, nat_trans.comp_app, category.assoc],
  dsimp,
  erw [limit.lift_π_assoc, category.id_comp],
  refl,
end

instance [is_filtered K] [fin_category J] (F : J ⥤ K ⥤ D) :
  is_iso (colimit_limit_to_limit_colimit' F) :=
by { delta colimit_limit_to_limit_colimit', apply_instance }

noncomputable
def colimit_limit_to_limit_colimit_of_is_limit (F : J ⥤ K ⥤ D)
  (E : cone F) (hE : is_limit E) :
  colimit E.X ⟶ limit (colimit F.flip) :=
(has_colimit.iso_of_nat_iso (hE.cone_point_unique_up_to_iso (limit.is_limit _))).hom ≫
colimit_limit_to_limit_colimit' F

@[simp, reassoc]
lemma ι_colimit_limit_to_limit_colimit_of_is_limit_π (F : J ⥤ K ⥤ D)
  (E : cone F) (hE : is_limit E) (k) (j) :
  colimit.ι E.X k ≫ colimit_limit_to_limit_colimit_of_is_limit F E hE ≫
  limit.π (colimit F.flip) j = (E.π.app j).app k ≫ (colimit.ι F.flip k).app j :=
begin
  dsimp only [colimit_limit_to_limit_colimit_of_is_limit,
    has_colimit.iso_of_nat_iso, is_colimit.cocone_points_iso_of_nat_iso,
    is_colimit.map],
  simp_rw ← category.assoc,
  erw colimit.ι_desc,
  dsimp only [cocones.precompose, is_limit.cone_point_unique_up_to_iso, functor.map_iso,
    cones.forget, nat_trans.comp_app],
  simp_rw category.assoc,
  erw [ι_colimit_limit_to_limit_colimit'_π, ← category.assoc, ← nat_trans.comp_app,
    (hE.unique_up_to_iso (limit.is_limit F)).hom.w j],
end

lemma is_iso_colimit_limit_to_limit_colimit_of_is_limit
  [is_filtered K] [fin_category J] (F : J ⥤ K ⥤ D) (E : cone F) (hE : is_limit E) :
  is_iso (colimit_limit_to_limit_colimit_of_is_limit F E hE) :=
by { delta colimit_limit_to_limit_colimit_of_is_limit, apply_instance }

/-
@[simps hom inv]
noncomputable
def colimit_limit_iso [is_filtered K] [fin_category J]
  (F : J ⥤ K ⥤ D) (E : cone F) (hE : is_limit E) :
  colimit E.X ≅ limit (colimit F.flip) :=
by letI := is_iso_colimit_limit_to_limit_colimit_of_is_limit F E hE;
  exact as_iso (colimit_limit_to_limit_colimit_of_is_limit F E hE)
-/

end limits

end category_theory
