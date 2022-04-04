import for_mathlib.derived.K_projective
import liquid
import Lbar.functor
import condensed.projective_resolution
import condensed.condensify
import breen_deligne.main
import breen_deligne.eg

noncomputable theory

universes v u

open opposite category_theory category_theory.limits
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

-- move me
instance Condensed_Ab_free_preserves_filtered_colimits :
  preserves_filtered_colimits (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_Condensed_Ab) :=
sorry

section

open bounded_homotopy_category

set_option pp.universes true

variables {𝒜 : Type u} [category.{v} 𝒜] [abelian 𝒜] [enough_projectives 𝒜]

local notation `to_bhc` := chain_complex.to_bounded_homotopy_category

-- A *proisomorphism* is a TODO
def is_proiso {𝒜 : Type*} [category 𝒜] {X Y : ℝ≥0ᵒᵖ ⥤ 𝒜} (f : X ⟶ Y) : Prop :=
sorry

lemma iso_of_proiso
  (𝓧 𝓨 : ℝ≥0 ⥤ chain_complex 𝒜 ℕ)
  (X : cocone 𝓧) (Y : cocone 𝓨) (hX : is_colimit X) (hY : is_colimit Y)
  (Z : bounded_homotopy_category 𝒜)
  (f' ι' : 𝓧 ⟶ 𝓨) (f ι : X.X ⟶ Y.X) (g : Z ⟶ Z)
  (hf' : hX.map _ f' = f) (hι' : hX.map _ ι' = ι)
  (H : ∀ i : ℤ, is_proiso
    ((whisker_right (nat_trans.op f') (to_bhc .op ⋙ (Ext i).flip.obj Z)) -
      (whisker_right (nat_trans.op ι') (to_bhc .op ⋙ (Ext i).flip.obj Z)) ≫
        ((whisker_left 𝓧.op (whisker_left to_bhc .op ((Ext i).flip.map g)))))) :
  ∀ i : ℤ, is_iso
    (((Ext i).map (to_bhc .map f).op).app Z -
      (((Ext i).map (to_bhc .map ι).op).app Z ≫
        ((Ext i).obj (op $ to_bhc .obj X.X)).map g)) :=
begin
  sorry
end

end

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem is_iso_Tinv_sub (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] :
  ∀ i, is_iso (Tinv_sub r r' S V i) :=
begin
  refine (breen_deligne.package.main_lemma breen_deligne.eg
    (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_Condensed_Ab)
    _ _ _ _).mpr _,
  sorry -- use `iso_of_proiso`
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
