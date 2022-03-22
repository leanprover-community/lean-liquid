import for_mathlib.derived.K_projective
import liquid
import Lbar.functor
import condensed.projective_resolution

noncomputable theory

universe u

open opposite category_theory
open_locale nnreal

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]

namespace Lbar

open ProFiltPseuNormGrpWithTinv₁ ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁

def condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
Lbar.functor.{u u} r' ⋙ to_PFPNG₁.{u} _ ⋙ to_CHFPNG₁.{u} ⋙ to_Condensed.{u}

def Tinv_nat_trans : Lbar.condensed.{u} r' ⟶ Lbar.condensed.{u} r' :=
begin
  refine @whisker_right _ _ _ _ _ _
    (Lbar.functor.{u u} r' ⋙ to_PFPNG₁.{u} _ ⋙ to_CHFPNG₁.{u} ⋙ enlarging_functor)
    (Lbar.functor.{u u} r' ⋙ to_PFPNG₁.{u} _ ⋙ to_CHFPNG₁.{u} ⋙ enlarging_functor)
    _
    CompHausFiltPseuNormGrp.to_Condensed,
  refine whisker_left (Lbar.functor.{u u} r')
  { app := _,
    naturality' := _ },
  { intro M, exact profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv },
  { intros M₁ M₂ f, ext x, exact (f.map_Tinv x).symm }
end

def Tinv_sub (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] (i : ℤ) :
  ((Ext' i).obj (op $ (Lbar.condensed.{u} r').obj S)).obj (Condensed.of_top_ab V) ⟶
  ((Ext' i).obj (op $ (Lbar.condensed.{u} r').obj S)).obj (Condensed.of_top_ab V) :=
((Ext' i).map ((Tinv_nat_trans r').app S).op).app _ -
((Ext' i).obj _).map (Condensed.of_top_ab_map (normed_with_aut.T.inv).to_add_monoid_hom
  (normed_group_hom.continuous _))
  -- this should be normed_with_aut.T.inv mapped through a functor

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem Ext_iso_zero (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] (i : ℤ) :
  is_iso (Tinv_sub r r' S V i) :=
sorry

end Lbar
