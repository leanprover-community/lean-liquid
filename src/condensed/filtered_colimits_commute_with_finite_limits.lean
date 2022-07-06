import condensed.top_comparison
import condensed.filtered_colimits

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
    naturality' := sorry }⟩,
  naturality' := sorry }⟩

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

end CondensedSet
