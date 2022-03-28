import for_mathlib.derived.K_projective
import liquid
import Lbar.functor
import condensed.projective_resolution
import condensed.condensify
import breen_deligne.main

noncomputable theory

universe u

open opposite category_theory
open_locale nnreal

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]

namespace Lbar

open ProFiltPseuNormGrpWithTinv₁ ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁

def condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
condensify (fintype_functor.{u u} r' ⋙ to_CHFPNG₁ r')

def Tinv_sub (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] (i : ℤ) :
  ((Ext' i).obj (op $ (Lbar.condensed.{u} r').obj S)).obj (Condensed.of_top_ab V) ⟶
  ((Ext' i).obj (op $ (Lbar.condensed.{u} r').obj S)).obj (Condensed.of_top_ab V) :=
((Ext' i).map ((condensify_Tinv _).app S).op).app _ -
((Ext' i).obj _).map (Condensed.of_top_ab_map (normed_with_aut.T.inv).to_add_monoid_hom
  (normed_group_hom.continuous _))

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem is_iso_Tinv_sub (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] :
  ∀ i, is_iso (Tinv_sub r r' S V i) :=
begin
  refine (breen_deligne.package.main_lemma _ _ _ _ _ _).mpr _,
  all_goals { sorry }
end

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem is_iso_Tinv2 (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] :
  ∀ i, is_iso (((Ext' i).map ((condensify_Tinv2 (Lbar.fintype_functor.{u u} r')).app S).op).app
    (Condensed.of_top_ab ↥V)) :=
begin
  rw [condensify_Tinv2, condensify_nonstrict_Tinv2],
  -- use that `Ext'.map` is additive (is that formalized already?)
  -- then repackage and use `is_iso_Tinv_sub` above
  sorry
end

end Lbar
