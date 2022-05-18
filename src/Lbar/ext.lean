import for_mathlib.derived.les_facts
import liquid
import Lbar.functor
import condensed.projective_resolution
import condensed.condensify
import breen_deligne.main
import breen_deligne.eg

import for_mathlib.derived.ext_coproducts
import condensed.ab4
import Lbar.squares
import pseudo_normed_group.QprimeFP
import for_mathlib.acyclic
import free_pfpng.acyclic

noncomputable theory

universes v u

set_option pp.universes true

open opposite category_theory category_theory.limits
open_locale nnreal

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]

abbreviation SemiNormedGroup.to_Cond (V : SemiNormedGroup.{u}) := Condensed.of_top_ab V

section

open bounded_homotopy_category

variables (BD : breen_deligne.data)
variables (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ (c : ℝ≥0), BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]

lemma ExtQprime_iso_aux_system_aux (c : ℝ≥0) (k i : ℤ) (hi : i > 0) :
  is_zero (((Ext' i).obj (op (((homological_complex.embed complex_shape.embedding.nat_down_int_up).obj
      ((QprimeFP_nat.{u} r' BD κ M).obj c)).X k))).obj V.to_Cond) :=
begin
  rcases k with (_|_)|_,
  { apply free_acyclic.{u} _ V i hi },
  { /- prove `Ext(0, V)` is zero -/ sorry },
  { apply free_acyclic.{u} _ V i hi },
end

def ExtQprime_iso_aux_system (c : ℝ≥0) (n : ℕ) :
  ((Ext n).obj (op $ (QprimeFP r' BD κ M).obj c)).obj ((single _ 0).obj V.to_Cond) ≅
  Ab.ulift.{u+1}.obj (((aux_system r' BD ⟨M⟩ V κ).to_AbH n).obj (op c)) :=
Ext_compute_with_acyclic _ _ (ExtQprime_iso_aux_system_aux r' BD κ M V c) _ ≪≫
  sorry

end

namespace Lbar

open ProFiltPseuNormGrpWithTinv₁ ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁

def condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
condensify (Fintype_Lbar.{u u} r' ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r')

def Tinv_sub (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] (i : ℤ) :
  ((Ext' i).obj (op $ (Lbar.condensed.{u} r').obj S)).obj (Condensed.of_top_ab V) ⟶
  ((Ext' i).obj (op $ (Lbar.condensed.{u} r').obj S)).obj (Condensed.of_top_ab V) :=
((Ext' i).map ((condensify_Tinv _).app S).op).app _ -
((Ext' i).obj _).map (Condensed.of_top_ab_map (normed_with_aut.T.inv).to_add_monoid_hom
  (normed_group_hom.continuous _))

-- move me
-- instance Condensed_Ab_free_preserves_filtered_colimits :
--   preserves_filtered_colimits (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_Condensed_Ab) :=
-- sorry

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem is_iso_Tinv_sub (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] :
  ∀ i, is_iso (Tinv_sub r r' S V i) :=
begin
  refine (breen_deligne.package.main_lemma breen_deligne.eg
    (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_Condensed_Ab)
    _ _ _ _).mpr _,
  sorry
end

-- move me
@[simp] lemma _root_.category_theory.op_nsmul
  {C : Type*} [category C] [preadditive C] {X Y : C} (n : ℕ) (f : X ⟶ Y) :
  (n • f).op = n • f.op := rfl

-- move me
@[simp] lemma _root_.category_theory.op_sub
  {C : Type*} [category C] [preadditive C] {X Y : C} (f g : X ⟶ Y) :
  (f - g).op = f.op - g.op := rfl

-- move me
attribute [simps] Condensed.of_top_ab_map

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem is_iso_Tinv2 (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V]
  (hV : ∀ (v : V), (normed_with_aut.T.inv v) = 2 • v) :
  ∀ i, is_iso (((Ext' i).map ((condensify_Tinv2 (Fintype_Lbar.{u u} r')).app S).op).app
    (Condensed.of_top_ab ↥V)) :=
begin
  intro i,
  rw [condensify_Tinv2_eq, ← functor.flip_obj_map, nat_trans.app_sub, category_theory.op_sub,
    nat_trans.app_nsmul,  category_theory.op_nsmul, two_nsmul, nat_trans.id_app, op_id,
    functor.map_sub, functor.map_add, category_theory.functor.map_id],
  convert is_iso_Tinv_sub r r' S V i using 2,
  suffices : Condensed.of_top_ab_map (normed_group_hom.to_add_monoid_hom normed_with_aut.T.inv) _ =
    2 • 𝟙 _,
  { rw [this, two_nsmul, functor.map_add, category_theory.functor.map_id], refl, },
  ext T f t,
  dsimp only [Condensed.of_top_ab_map_val, whisker_right_app, Ab.ulift_map_apply_down,
    add_monoid_hom.mk'_apply, continuous_map.coe_mk, function.comp_app],
  erw [hV, two_nsmul, two_nsmul],
  refl,
end

end Lbar
