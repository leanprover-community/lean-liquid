import condensed.top_comparison
import condensed.filtered_colimits
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

lemma is_iso_colim_to_lim_component (S : Profinite.{u}ᵒᵖ) :
  is_iso ((colim_to_lim F).val.app S) :=
begin
  /-
  The forgetful functor to presheaves preserves filtered colimits and all limits,
  while the same holds for evaluation, hence this morphism should be isomoprhic to
  `colimit_limit_to_limit_colimit` which is an isomorphism.
  -/
  sorry
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
