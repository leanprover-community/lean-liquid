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
import for_mathlib.SemiNormedGroup_ulift

noncomputable theory

universes u

set_option pp.universes true

open opposite category_theory category_theory.limits
open_locale nnreal

variables (r r' : ℝ≥0)
variables [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r < 1)] [fact (r' < 1)]

abbreviation SemiNormedGroup.to_Cond (V : SemiNormedGroup.{u}) := Condensed.of_top_ab V

section

open bounded_homotopy_category

variables (BD : breen_deligne.data)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]

-- move me
lemma Ext'_zero_left_is_zero {𝓐 : Type*} [category 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
  (A : 𝓐ᵒᵖ) (B : 𝓐) (hA : is_zero A) (i : ℤ) :
  is_zero (((Ext' i).obj A).obj B) :=
begin
  rw is_zero_iff_id_eq_zero at hA ⊢,
  rw [← functor.flip_obj_obj, ← category_theory.functor.map_id, hA, functor.map_zero],
end

lemma ExtQprime_iso_aux_system_aux (c : ℝ≥0) (k i : ℤ) (hi : i > 0) :
  is_zero (((Ext' i).obj (op (((homological_complex.embed complex_shape.embedding.nat_down_int_up).obj
      ((QprimeFP_nat.{u} r' BD κ M).obj c)).X k))).obj V.to_Cond) :=
begin
  rcases k with (_|_)|_,
  { apply free_acyclic.{u} _ V i hi },
  { apply Ext'_zero_left_is_zero, refine (is_zero_zero _).op },
  { apply free_acyclic.{u} _ V i hi },
end

-- this needs to be functorial in `c`
def ExtQprime_iso_aux_system_obj (c : ℝ≥0) (n : ℕ) :
  ((Ext n).obj (op $ (QprimeFP r' BD κ M).obj c)).obj ((single _ 0).obj V.to_Cond) ≅
  ((aux_system r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ).to_AbH n).obj (op c) :=
Ext_compute_with_acyclic _ _ (ExtQprime_iso_aux_system_aux r' BD κ M V c) _ ≪≫
  sorry

def ExtQprime_iso_aux_system (n : ℕ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ≅
  aux_system r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ ⋙
    (forget₂ _ Ab).map_homological_complex _ ⋙ homology_functor _ _ n :=
sorry

/-- The `Tinv` map induced by `M` -/
def ExtQprime.Tinv
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (n : ℕ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ⟶
  (QprimeFP r' BD κ₂ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) :=
sorry

/-- The `T_inv` map induced by `V` -/
def ExtQprime.T_inv [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (n : ℕ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ⟶
  (QprimeFP r' BD κ₂ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) :=
sorry

def ExtQprime.Tinv2 [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (n : ℕ) :
  (QprimeFP r' BD κ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) ⟶
  (QprimeFP r' BD κ₂ M).op ⋙ (Ext n).flip.obj ((single _ 0).obj V.to_Cond) :=
ExtQprime.Tinv r' BD κ κ₂ M V n - ExtQprime.T_inv r r' BD κ κ₂ M V n

lemma ExtQprime_iso_aux_system_comm [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)] (n : ℕ) :
  (ExtQprime_iso_aux_system r' BD κ M V n).hom ≫
  whisker_right (aux_system.Tinv2.{u} r r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ₂ κ)
    ((forget₂ _ _).map_homological_complex _ ⋙ homology_functor Ab.{u+1} (complex_shape.up ℕ) n) =
  ExtQprime.Tinv2 r r' BD κ κ₂ M V n ≫
  (ExtQprime_iso_aux_system r' BD κ₂ M V n).hom :=
sorry

lemma ExtQprime_iso_aux_system_comm' [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)] (n : ℕ) :
  whisker_right (aux_system.Tinv2.{u} r r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1}.obj V) κ₂ κ)
    ((forget₂ _ _).map_homological_complex _ ⋙ homology_functor Ab.{u+1} (complex_shape.up ℕ) n) ≫
  (ExtQprime_iso_aux_system r' BD κ₂ M V n).inv =
  (ExtQprime_iso_aux_system r' BD κ M V n).inv ≫
  ExtQprime.Tinv2 r r' BD κ κ₂ M V n :=
begin
  rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp],
  apply ExtQprime_iso_aux_system_comm
end

end

section

variables {r'}
variables (BD : breen_deligne.package)
variables (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)
variables [∀ (c : ℝ≥0), BD.data.suitable (κ c)] [∀ n, fact (monotone (function.swap κ n))]
variables [∀ (c : ℝ≥0), BD.data.suitable (κ₂ c)] [∀ n, fact (monotone (function.swap κ₂ n))]
variables (M : ProFiltPseuNormGrpWithTinv₁.{u} r')
variables (V : SemiNormedGroup.{u}) [complete_space V] [separated_space V]

open bounded_homotopy_category

-- move me
/-- `Tinv : M → M` as hom of condensed abelian groups -/
def _root_.ProFiltPseuNormGrpWithTinv₁.Tinv_cond : M.to_Condensed ⟶ M.to_Condensed :=
(CompHausFiltPseuNormGrp.to_Condensed.{u}).map
  profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv

variables (ι : ulift.{u+1} ℕ → ℝ≥0) (hι : monotone ι)

lemma Tinv2_iso_of_bicartesian [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (i : ℕ)
  (H1 : (shift_sub_id.commsq (ExtQprime.Tinv2 r r' BD.data κ κ₂ M V i) ι hι).bicartesian)
  (H2 : (shift_sub_id.commsq (ExtQprime.Tinv2 r r' BD.data κ κ₂ M V (i+1)) ι hι).bicartesian) :
  is_iso (((Ext (i+1)).map ((BD.eval freeCond'.{u}).op.map M.Tinv_cond.op)).app
    ((single (Condensed Ab) 0).obj V.to_Cond) -
    ((Ext (i+1)).obj ((BD.eval freeCond').op.obj (op (M.to_Condensed)))).map
      ((single (Condensed Ab) 0).map
        (Condensed.of_top_ab_map
          (normed_group_hom.to_add_monoid_hom normed_with_aut.T.inv) (normed_group_hom.continuous _)))) :=
sorry

lemma Tinv2_iso_of_bicartesian_0 [normed_with_aut r V]
  [∀ c n, fact (κ₂ c n ≤ κ c n)] [∀ c n, fact (κ₂ c n ≤ r' * κ c n)]
  (H1 : (shift_sub_id.commsq (ExtQprime.Tinv2 r r' BD.data κ κ₂ M V 0) ι hι).bicartesian) :
  is_iso (((Ext 0).map ((BD.eval freeCond'.{u}).op.map M.Tinv_cond.op)).app
    ((single (Condensed Ab) 0).obj V.to_Cond) -
    ((Ext 0).obj ((BD.eval freeCond').op.obj (op (M.to_Condensed)))).map
      ((single (Condensed Ab) 0).map
        (Condensed.of_top_ab_map
          (normed_group_hom.to_add_monoid_hom normed_with_aut.T.inv) (normed_group_hom.continuous _)))) :=
sorry

end

namespace Lbar

open ProFiltPseuNormGrpWithTinv₁ ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁
open bounded_homotopy_category

def condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
condensify (Fintype_Lbar.{u u} r' ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r')

def Tinv_sub (S : Profinite.{u}) (V : SemiNormedGroup.{u}) [normed_with_aut r V] (i : ℤ) :
  ((Ext' i).obj (op $ (Lbar.condensed.{u} r').obj S)).obj V.to_Cond ⟶
  ((Ext' i).obj (op $ (Lbar.condensed.{u} r').obj S)).obj V.to_Cond :=
((Ext' i).map ((condensify_Tinv _).app S).op).app _ -
((Ext' i).obj _).map (Condensed.of_top_ab_map (normed_with_aut.T.inv).to_add_monoid_hom
  (normed_group_hom.continuous _))

-- move me
-- instance Condensed_Ab_free_preserves_filtered_colimits :
--   preserves_filtered_colimits (Condensed_Ab_to_CondensedSet ⋙ CondensedSet_to_Condensed_Ab) :=
-- sorry

set_option pp.universes true

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

variables (S : Profinite.{0}) (V : SemiNormedGroup.{0})
variables [complete_space V] [separated_space V]

-- This is not true. But the two objects are naturally isomorphic. We'll have to deal with that.
example :
  (condensify (Fintype_Lbar.{0 0} r' ⋙ PFPNGT₁_to_CHFPNG₁ₑₗ r')).obj S =
  ((Profinite.extend (Fintype_Lbar.{0 0} r')).obj S).to_Condensed :=
sorry

variables (i : ℕ) (ι : ulift.{1} ℕ → ℝ≥0) (hι : monotone ι)

def useful_commsq [normed_with_aut r V] :=
  shift_sub_id.commsq
    (ExtQprime.Tinv2 r r' breen_deligne.eg.data
      (λ c n, c * breen_deligne.eg.κ r r' n)
      (λ c n, r' * (c * breen_deligne.eg.κ r r' n))
      ((Lbar.functor.{0 0} r').obj S) V i) ι hι

lemma useful_commsq_bicartesian [normed_with_aut r V] :
  (useful_commsq r r' S V i ι hι).bicartesian :=
begin
  apply shift_sub_id.bicartesian_iso _ _
    (ExtQprime_iso_aux_system r' _ _ _ V i).symm (ExtQprime_iso_aux_system r' _ _ _ V i).symm ι hι
    (ExtQprime_iso_aux_system_comm' _ _ _ _ _ _ _ _),
  rw [← whisker_right_twice],
  refine shift_sub_id.bicartesian (aux_system.incl'.{0 1} r r' _ _ _ (breen_deligne.eg.κ r r')) _
    i ι hι _ _ _,
  { apply_with system_of_complexes.shift_eq_zero {instances := ff},
    swap 3, { apply thm94.explicit r r' _ _ (breen_deligne.eg.κ' r r'), },
    any_goals { apply_instance },
    -- we need to put assumptions on `ι` to make these true
    -- but it's clear that there will always be a `ι` that works
    sorry, sorry },
  { apply_with system_of_complexes.shift_eq_zero {instances := ff},
    swap 3, { apply thm94.explicit r r' _ _ (breen_deligne.eg.κ' r r'), },
    any_goals { apply_instance },
    -- we need to put assumptions on `ι` to make these true
    -- but it's clear that there will always be a `ι` that works
    sorry, sorry },
  { intros c n,
    let κ := breen_deligne.eg.κ r r',
    apply aux_system.short_exact r r' _ _ _ (λ c n, r' * (c * κ n)) κ,
    intro c, dsimp, apply_instance, }
end

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem is_iso_Tinv_sub [normed_with_aut r V] : ∀ i, is_iso (Tinv_sub r r' S V i) :=
begin
  refine (breen_deligne.package.main_lemma breen_deligne.eg freeCond' _ _ _ _).mpr _,
  rintro ((_|_)|_),
  { sorry },
  { sorry },
  { have : 1 + -[1+ i] ≤ 0,
    { rw [int.neg_succ_of_nat_eq'],
      simp only [add_sub_cancel'_right, right.neg_nonpos_iff, int.coe_nat_nonneg] },
    apply is_zero.is_iso;
    apply Ext_single_right_is_zero _ _ 1 _ _ (chain_complex.bounded_by_one _) this },
end

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem is_iso_Tinv2 [normed_with_aut r V]
  (hV : ∀ (v : V), (normed_with_aut.T.inv v) = 2 • v) :
  ∀ i, is_iso (((Ext' i).map ((condensify_Tinv2 (Fintype_Lbar.{0 0} r')).app S).op).app
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
