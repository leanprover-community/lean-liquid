import condensed.filtered_colimits_commute_with_finite_limits
import condensed.ab
import for_mathlib.nnreal_to_nat_colimit

open category_theory
open category_theory.limits

namespace Condensed

open_locale nnreal

noncomputable theory

universes u
variables (F : Condensed.{u} Ab.{u+1} ⥤ Condensed.{u} Ab.{u+1})
  [preserves_filtered_colimits F] (A : CompHausFiltPseuNormGrp.{u})
  (c : ℝ≥0) [fact (0 < c)]

/-
Remark: In practice, `F` is going to be
`Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_Condensed_Ab`
-/

set_option pp.universes true

def as_nat_diagram : as_small.{u+1} ℕ ⥤ CondensedSet.{u} :=
restrict_diagram c A.level_Condensed_diagram'

@[simp, reassoc]
lemma ι_colimit_iso_Condensed_obj (i) :
  colimit.ι _ i ≫ A.colimit_iso_Condensed_obj.hom =
  A.level_Condensed_diagram_cocone.ι.app _ :=
begin
  dsimp [CompHausFiltPseuNormGrp.colimit_iso_Condensed_obj],
  erw colimit.ι_desc_assoc,
  apply CondensedSet_to_presheaf.map_injective,
  dsimp [CompHausFiltPseuNormGrp.colimit_iso_Condensed_obj_aux_nat_iso],
  ext S : 2, dsimp,
  erw
    ((is_colimit_of_preserves.{u+1 u+1 u+1 u+1 u+2 u+2}
    ((category_theory.evaluation.{u u+1 u+1 u+2} Profinite.{u}ᵒᵖ
    (Type (u+1))).obj S) (colimit.is_colimit.{u+1 u+1 u+1 u+2}
    (A.level_Condensed_diagram' ⋙ Sheaf_to_presheaf.{u u+1 u+1 u+2}
    proetale_topology.{u} (Type (u+1)))))).fac_assoc,
  erw colimit.ι_desc_assoc,
  refl,
end

def is_colimit_level_Condensed_diagram_cocone :
  is_colimit A.level_Condensed_diagram_cocone :=
{ desc := λ S, A.colimit_iso_Condensed_obj.inv ≫ colimit.desc _ S,
  fac' := begin
    intros S j, rw ← category.assoc,
    let t := _, change t ≫ _ = _,
    have ht : t = colimit.ι _ _,
    { dsimp [t], rw [iso.comp_inv_eq, ι_colimit_iso_Condensed_obj] },
    simp [ht],
  end,
  uniq' := begin
    intros S m hm,
    rw iso.eq_inv_comp,
    apply colimit.hom_ext, intros j,
    specialize hm j,
    simpa,
  end }

def as_nat_cocone : cocone (as_nat_diagram A c) :=
restrict_cocone c A.level_Condensed_diagram_cocone

def is_colimit_as_nat_cocone : is_colimit (as_nat_cocone A c) :=
is_colimit_restrict_cocone c _ (is_colimit_level_Condensed_diagram_cocone _)

end Condensed
