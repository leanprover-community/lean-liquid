import for_mathlib.homological_complex_op

import pseudo_normed_group.FP2
import pseudo_normed_group.system_of_complexes

import system_of_complexes.rescale

noncomputable theory

open_locale nnreal

universes u v

open category_theory breen_deligne

lemma category_theory.unop_sum {C : Type*} [category C] [preadditive C] {X Y : Cᵒᵖ}
  {ι : Type*} (s : finset ι) (f : ι → (X ⟶ Y)) :
  (s.sum f).unop = s.sum (λ i, (f i).unop) :=
begin
  classical,
  refine finset.induction_on s (by simp) _,
  intros,
  simp only [*, finset.sum_insert, not_false_iff, unop_add],
end

lemma category_theory.unop_zsmul {C : Type*} [category C] [preadditive C] {X Y : Cᵒᵖ}
  (k : ℤ) (f : X ⟶ Y) : (k • f).unop = k • f.unop := rfl

variables (r r' : ℝ≥0)
variables (BD : breen_deligne.data) (κ : ℕ → ℝ≥0) [BD.suitable κ]
variables (M : ProFiltPseuNormGrpWithTinv.{u} r')
variables (V : SemiNormedGroup.{v})

set_option pp.universes true

def aux_system : system_of_complexes :=
(FPsystem r' BD κ M).op ⋙
  (((CLC.{v u} V).right_op.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _).op ⋙
  homological_complex.unop_functor

namespace aux_system

variables [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)]

open system_of_complexes opposite

def Tinv : aux_system r' BD κ M V ⟶ (ScaleIndexLeft r').obj (aux_system r' BD κ M V) :=
@whisker_right _ _ _ _ _ _ (FPsystem r' BD κ M).op ((nnreal.MulLeft r').op ⋙ (FPsystem r' BD κ M).op)
  (nat_trans.op $ FPsystem.Tinv r' BD κ M)
  ((((CLC.{v u} V).right_op.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _).op ⋙
    homological_complex.unop_functor)

def T_inv [normed_with_aut r V] : aux_system r' BD κ M V ⟶ aux_system r' BD κ M V :=
{ app := λ c,
  { f := λ i, normed_group_hom.completion $ (SemiNormedGroup.LocallyConstant.map $ normed_with_aut.T.inv).app _,
    comm' := begin
      rintro i j (rfl : i + 1 = j),
      dsimp only [aux_system, functor.comp_obj, homological_complex.unop_functor,
        homological_complex.unop_d, functor.op_obj, functor.map_homological_complex_obj_d,
        unop_op],
      erw [← SemiNormedGroup.Completion_map, ← SemiNormedGroup.Completion_map, chain_complex.of_d],
      dsimp only [FPsystem.d, universal_map.eval_FP2, universal_map.eval_CLCFP,
        universal_map.eval_LCFP, CLC],
      simp only [nat_trans.app_sum, functor.map_sum, preadditive.comp_sum, preadditive.sum_comp,
        category_theory.unop_sum, nat_trans.app_zsmul, functor.map_zsmul,
        preadditive.comp_zsmul, preadditive.zsmul_comp, category_theory.unop_zsmul],
      refine finset.sum_congr rfl _,
      rintro ⟨g, hg⟩ -,
      dsimp only [basic_universal_map.eval_FP2, basic_universal_map.eval_LCFP,
        whisker_right_app, nat_trans.op_app, unop_op, FreeAb.of_functor,
        free_abelian_group.map_of_apply, functor.right_op_map, LC,
        functor.comp_map, functor.map_FreeAb, FreeAb.eval],
      rw [free_abelian_group.lift.of, _root_.id, quiver.hom.unop_op,
        ← SemiNormedGroup.Completion.map_comp, ← SemiNormedGroup.Completion.map_comp,
        nat_trans.naturality],
    end },
  naturality' := λ c₁ c₂ h, begin
    ext n : 2,
    dsimp only [homological_complex.comp_f, aux_system, functor.comp_map, homological_complex.unop_functor,
      homological_complex.unop_d, functor.op_obj, functor.map_homological_complex_obj_d,
      unop_op, CLC, functor.op_map, quiver.hom.unop_op, functor.map_homological_complex_map_f,
      functor.map_FreeAb, FreeAb.eval, free_abelian_group.map_of_apply,
      FPsystem, FP2.res_app, FreeAb.of_functor, functor.right_op_map],
    rw [← SemiNormedGroup.Completion_map, ← SemiNormedGroup.Completion_map,
      free_abelian_group.lift.of, _root_.id, quiver.hom.unop_op,
      ← SemiNormedGroup.Completion.map_comp, ← SemiNormedGroup.Completion.map_comp,
        nat_trans.naturality],
    refl,
  end }

def res : aux_system r' BD κ M V ⟶ (ScaleIndexLeft r').obj (aux_system r' BD κ M V) :=
@whisker_right _ _ _ _ _ _ (FPsystem r' BD κ M).op ((nnreal.MulLeft r').op ⋙ (FPsystem r' BD κ M).op)
  (nat_trans.op $ FPsystem.res r' BD κ M)
  ((((CLC.{v u} V).right_op.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _).op ⋙
    homological_complex.unop_functor)

variables [normed_with_aut r V]

def Tinv2 :
  aux_system r' BD κ M V ⟶ (ScaleIndexLeft r').obj (aux_system r' BD κ M V) :=
Tinv r' BD κ M V - T_inv r r' BD κ M V ≫ res r' BD κ M V

-- def incl : (data.system BD κ r V r').obj (op M) ⟶ aux_system r' BD κ M V :=
-- { app := λ c, begin
--     delta data.system,
--   end,
--   naturality' := _ }

-- lemma short_exact (c : ℝ≥0) (n : ℕ) :
--   short_exact










-- lemma T_inv_aux2 (c₁ c₂ : ℝ≥0) (m n : ℕ)
--   (g : basic_universal_map m n) [g.suitable c₁ c₂] (k : ℤ) :
--   (free_abelian_group.lift id (free_abelian_group.map
--     (@category_theory.functor.map _ _ _ _ (CLC V).right_op _ _)
--       ((k • basic_universal_map.eval_FP2 r' g c₁ c₂).app M))).unop =
--   normed_group_hom_completion_hom ((k • basic_universal_map.eval_LCFP V r' g c₂ c₁).app (op M)) :=
-- begin
--   simp only [nat_trans.app_zsmul, map_zsmul, category_theory.unop_zsmul],
--   dsimp only [basic_universal_map.eval_FP2, basic_universal_map.eval_LCFP,
--     whisker_right_app, nat_trans.op_app, unop_op, FreeAb.of_functor,
--     free_abelian_group.map_of_apply],
--   rw [free_abelian_group.lift.of],
--   refl,
-- end

-- lemma T_inv_aux (c : ℝ≥0ᵒᵖ) (i : ℕ) :
--   arrow.mk (((aux_system r' BD κ M V).obj c).d i (i + 1)) =
--   arrow.mk ((universal_map.eval_CLCFP V r' (unop c * κ i) (unop c * κ (i + 1)) (BD.d (i + 1) i) : _).app (op M)) :=
-- begin
--   dsimp [aux_system, FPsystem],
--   rw [chain_complex.of_d],
--   dsimp [FreeAb.eval, functor.map_FreeAb, functor.right_op_map, FPsystem.d,
--     universal_map.eval_FP2, universal_map.eval_CLCFP, universal_map.eval_LCFP],
--   simp only [nat_trans.app_sum, map_sum, ← normed_group_hom_completion_hom_apply,
--     category_theory.unop_sum],
--   congr' 1,
--   refine finset.sum_congr rfl _,
--   rintro ⟨g, hg⟩ -,
--   apply T_inv_aux2,
-- end

-- def T_inv [fact (0 < r)] [normed_with_aut r V] : aux_system r' BD κ M V ⟶ aux_system r' BD κ M V :=
-- { app := λ c,
--   { f := λ i, ((CLCFP.T_inv r V r' (unop c * κ i) (BD.X i)).app (op M) : _),
--     comm' := begin
--       rintro i j (rfl : i + 1 = j),
--       have := congr_arg (λ α, nat_trans.app α (op M))
--         (universal_map.T_inv_comp_eval_CLCFP r V r' (unop c * κ i) ((unop c * κ (i+1))) (BD.d (i+1) i)),
--       dsimp only at this,
--       simp only [nat_trans.comp_app] at this,
--       convert this using 2;
--       apply arrow.mk_injective; apply T_inv_aux
--     end },
--   naturality' := λ c₁ c₂ h, begin
--     ext n : 2,
--     dsimp only [homological_complex.comp_f, aux_system, FPsystem, functor.comp_map],
--   end }

end aux_system
