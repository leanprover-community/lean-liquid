import condensed.top_comparison
import condensed.filtered_colimits
import condensed.adjunctions
import for_mathlib.pow_functor

open category_theory
open category_theory.limits

namespace CondensedSet

universes u

variables {J K : Type (u+1)} [small_category J] [small_category K]
  [is_filtered J] [fin_category K] (F : K ⥤ J ⥤ CondensedSet.{u})

noncomputable
def colim_to_lim :
  colimit (limit F) ⟶ limit (colimit F.flip) :=
colimit.desc (limit F) ⟨limit (colimit F.flip),
{ app := λ j, limit.lift (colimit F.flip) ⟨(limit F).obj j,
  { app := λ k, (limit.π F k).app j ≫ (colimit.ι F.flip j).app k,
    naturality' := λ X Y f, by begin
      erw [functor.const.obj_map, category.id_comp, category.assoc],
      rw [← nat_trans.naturality, ← category.assoc],
      simp only [functor.flip_obj_map, ← nat_trans.comp_app, limit.w],
    end }⟩,
  naturality' := λ X Y f, begin
    erw [functor.const.obj_map, category.comp_id],
    apply limit.hom_ext, intro k,
    simp only [category.assoc, limit.lift_π, nat_trans.naturality_assoc],
    simp only [← functor.flip_map_app, ← nat_trans.comp_app, colimit.w],
  end }⟩

noncomputable
instance preserves_filtered_colimits :
  preserves_filtered_colimits CondensedSet_to_presheaf.{u} :=
begin
  constructor, introsI J _ _, constructor, intros F,
  apply preserves_colimit_of_preserves_colimit_cocone
    (filtered_cocone_is_colimit F),
  let e : CondensedSet_to_presheaf.map_cocone (filtered_cocone F) ≅ colimit.cocone _ :=
    cocones.ext (iso.refl _) _,
  swap,
  { intros j, dsimp, simpa },
  apply is_colimit.of_iso_colimit _ e.symm,
  exact colimit.is_colimit _,
end

instance full_CondesensedSet_to_presheaf :
  full CondensedSet_to_presheaf :=
show full (Sheaf_to_presheaf _ _), by apply_instance

instance faithful_CondesensedSet_to_presheaf :
  faithful CondensedSet_to_presheaf :=
show faithful (Sheaf_to_presheaf _ _), by apply_instance

noncomputable
instance preserves_limits_CondesensedSet_to_presheaf :
  preserves_limits CondensedSet_to_presheaf :=
adjunction.right_adjoint_preserves_limits CondensedSet_presheaf_adjunction

section

noncomputable theory

-- set_option pp.universes true

def _root_.category_theory.functor.map_limit {C D J : Type*}
  [category C] [category D] [small_category J]
  (G : C ⥤ D) (F : J ⥤ C)
  [has_limit F] [has_limit (F ⋙ G)] [preserves_limit F G] :
  G.obj (limit F) ≅ limit (F ⋙ G) :=
is_limit.cone_point_unique_up_to_iso
  (is_limit_of_preserves G (limit.is_limit _))
  (limit.is_limit _)

def _root_.category_theory.functor.map_colimit {J C D : Type*}
  [small_category J] [category C] [category D]
  (G : C ⥤ D) (F : J ⥤ C)
  [has_colimit F] [has_colimit (F ⋙ G)] [preserves_colimit F G] :
  G.obj (colimit F) ≅ colimit (F ⋙ G) :=
is_colimit.cocone_point_unique_up_to_iso
  (is_colimit_of_preserves G (colimit.is_colimit _))
  (colimit.is_colimit _)

@[simp, reassoc]
lemma _root_.category_theory.functor.ι_map_colimit_inv {J C D : Type*}
  [small_category J] [category C] [category D]
  (G : C ⥤ D) (F : J ⥤ C)
  [has_colimit F] [has_colimit (F ⋙ G)] [preserves_colimit F G]
  (j : J) :
  colimit.ι (F ⋙ G) j ≫ (G.map_colimit F).inv = G.map (colimit.ι F j) :=
by simp only [category_theory.functor.map_colimit, functor.map_cocone_ι_app,
    colimit.comp_cocone_point_unique_up_to_iso_inv, colimit.cocone_ι]

def colimit_comp_iso {J K C D : Type*} [small_category J] [small_category K]
  [category C] [category D] [has_colimits_of_shape J D]
  (F : J ⥤ K ⥤ C) (G : C ⥤ D) [has_colimit F]
  [∀ k, has_colimit (F.flip.obj k)] [∀ k, preserves_colimit (F.flip.obj k) G]
  [∀ k, preserves_colimit F ((category_theory.evaluation K C).obj k)]
  [∀ k, has_colimit (F ⋙ (category_theory.evaluation K C).obj k)] :
  colimit F ⋙ G ≅ F.flip ⋙ ((whiskering_right _ _ _).obj G) ⋙ colim :=
begin
  refine nat_iso.of_components _ _,
  { intro k,
    refine G.map_iso _ ≪≫ G.map_colimit _,
    refine ((category_theory.evaluation _ _).obj k).map_colimit _, },
  { intros k₁ k₂ f,
    rw [← iso.inv_comp_eq, ← category.assoc, ← iso.eq_comp_inv],
    ext j,
    dsimp,
    simp only [category.assoc, category_theory.functor.ι_map_colimit_inv_assoc, colimit.ι_map_assoc,
      whisker_right_app, functor.flip_map_app],
    simp only [← functor.map_comp], congr' 1,
    sorry }
end
.

lemma is_iso_colim_to_lim_component (S : Profinite.{u}ᵒᵖ) :
  is_iso ((colim_to_lim F).val.app S) :=
begin
  /-
  The forgetful functor to presheaves preserves filtered colimits and all limits,
  while the same holds for evaluation, hence this morphism should be isomorphic to
  `colimit_limit_to_limit_colimit` which is an isomorphism.
  -/
  let VS := CondensedSet_to_presheaf.{u} ⋙ (category_theory.evaluation.{u u+1 u+1 u+2} Profinite.{u}ᵒᵖ (Type (u+1))).obj S,
  let F' := uncurry.{u+1 u+1}.obj F ⋙ VS,
  let f := colimit_limit_to_limit_colimit F',
  let e₁ : (colimit (limit F)).val.obj S ≅ colimit (curry.obj (category_theory.prod.swap J K ⋙ F') ⋙ lim),
  { sorry },
  let e₂ : (limit (colimit F.flip)).val.obj S ≅ limit (curry.obj F' ⋙ colim),
  { refine VS.map_limit (colimit F.flip) ≪≫ _,
    refine limits.lim.map_iso _,
    refine (colimit_comp_iso _ _) ≪≫ _,
    sorry },
  suffices : (colim_to_lim F).val.app S = e₁.hom ≫ f ≫ e₂.inv,
  { rw [this, is_iso_iff_is_iso_comp_left, is_iso_iff_is_iso_comp_right], apply_instance },
  sorry
end

end

lemma is_iso_colim_to_lim :
  is_iso (colim_to_lim F) :=
begin
  suffices : is_iso (CondensedSet_to_presheaf.map (colim_to_lim F)),
  { resetI, apply is_iso_of_fully_faithful CondensedSet_to_presheaf },
  apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
  intros S,
  apply is_iso_colim_to_lim_component,
end

noncomputable
def colimit_limit_iso_limit_colimit :
  colimit (limit F) ≅ limit (colimit F.flip) :=
@as_iso _ _ _ _ (colim_to_lim F) (is_iso_colim_to_lim _)

open_locale classical

-- How is this now showing up?
--instance fin_category_discrete (α : Type (u+1)) [fintype α] : fin_category (discrete α) :=
--sorry

noncomputable
def colimit_pow_iso (α : Type (u+1)) [fintype α] (F : J ⥤ CondensedSet.{u}) :
  colimit (∏ λ i : α, F) ≅ ∏ (λ i : α, colimit F) :=
colimit_limit_iso_limit_colimit (discrete.functor $ λ i : α, F) ≪≫
has_limit.iso_of_nat_iso (discrete.nat_iso $ λ i,
begin
  dsimp,
  refine (preserves_colimit_iso ((category_theory.evaluation _ _).obj i) _) ≪≫ _,
  refine has_colimit.iso_of_nat_iso _,
  refine nat_iso.of_components (λ j, iso.refl _) _,
  intros j k f, dsimp, simp,
end)

.

def is_colimit_pow_functor_map_cocone (α: Type (u+1))
  [fintype α]
  [J: Type (u+1)]
  [small_category J]
  [is_filtered J]
  (F: J ⥤ CondensedSet) :
  is_colimit ((pow_functor CondensedSet α).map_cocone (colimit.cocone F)) :=
sorry

-- Filtered colimits commute with finite products in condensed sets
noncomputable
instance pow_functor_preserves_filtered_colimits (α : Type (u+1)) [fintype α] :
  preserves_filtered_colimits
  (pow_functor CondensedSet.{u} α) :=
begin
  constructor, introsI J _ _, constructor, intros F,
  apply preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit F),
  apply is_colimit_pow_functor_map_cocone,
end

end CondensedSet
