import for_mathlib.exact_filtered_colimits
import condensed.exact
import condensed.top_comparison

open category_theory
open category_theory.limits

namespace Condensed

universes u

variables {J : Type (u+1)} [small_category J] [is_filtered J]

-- Axiom AB5 for `Condensed Ab`
theorem exact_colim_of_exact_of_is_filtered
  (F G H : J ⥤ Condensed.{u} Ab.{u+1}) (η : F ⟶ G) (γ : G ⟶ H) :
  (∀ j, exact (η.app j) (γ.app j)) → exact (limits.colim_map η) (limits.colim_map γ) :=
begin
  intros h,
  simp_rw condensed.exact_iff_ExtrDisc at *, intros S,
  let eF : (colimit F).val.obj (ExtrDisc_to_Profinite.op.obj (opposite.op S)) ≅
    colimit (F ⋙ Condensed.evaluation _ S.val) :=
    preserves_colimit_iso (Condensed.evaluation _ S.val) _,
  let eG : (colimit G).val.obj (ExtrDisc_to_Profinite.op.obj (opposite.op S)) ≅
    colimit (G ⋙ Condensed.evaluation _ S.val) :=
    preserves_colimit_iso (Condensed.evaluation _ S.val) _,
  let eH : (colimit H).val.obj (ExtrDisc_to_Profinite.op.obj (opposite.op S)) ≅
    colimit (H ⋙ Condensed.evaluation _ S.val) :=
    preserves_colimit_iso (Condensed.evaluation _ S.val) _,
  let t := _, let s := _, change exact s t,
  let ηS : F ⋙ Condensed.evaluation _ S.val ⟶ G ⋙ Condensed.evaluation _ S.val :=
    whisker_right η _,
  let γS : G ⋙ Condensed.evaluation _ S.val ⟶ H ⋙ Condensed.evaluation _ S.val :=
    whisker_right γ _,
  have hs : s = eF.hom ≫ colim_map ηS ≫ eG.inv,
  { rw [← iso.inv_comp_eq],
    dsimp [s, eG, eF, ηS],
    ext1,
    simp only [ι_preserves_colimits_iso_inv_assoc, evaluation_map, ι_colim_map_assoc,
      whisker_right_app, ι_preserves_colimits_iso_inv],
    simp only [← nat_trans.comp_app, ← Sheaf.hom.comp_val], congr' 2,
    simp },
  have ht : t = eG.hom ≫ colim_map γS ≫ eH.inv,
  { rw [← iso.inv_comp_eq],
    dsimp [t, eG, eH, γS],
    ext1,
    simp only [ι_preserves_colimits_iso_inv_assoc, evaluation_map, ι_colim_map_assoc,
      whisker_right_app, ι_preserves_colimits_iso_inv],
    simp only [← nat_trans.comp_app, ← Sheaf.hom.comp_val], congr' 2,
    simp },
  rw [hs, ht],
  rw [exact_iso_comp, ← category.assoc, exact_comp_iso],
  -- we have exact_comp_hom_inv_comp_iff, but missing exact_comp_inv_hom_comp_iff...
  rw [← iso.symm_hom],
  nth_rewrite 1 ← iso.symm_inv,
  rw exact_comp_hom_inv_comp_iff,
  apply AddCommGroup.exact_colim_of_exact_of_is_filtered, intros j, apply h,
end

instance AB5 : AB5 (Condensed.{u} Ab.{u+1}) :=
begin
  constructor, introsI J _ _, constructor, intros F G H f g h,
  apply exact_colim_of_exact_of_is_filtered,
  exact (nat_trans.exact_iff_forall.{(u+2) (u+1) (u+1)} f g).1 h,
end

end Condensed
