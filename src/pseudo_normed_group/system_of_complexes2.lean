import for_mathlib.homological_complex_op
import for_mathlib.split_exact
import for_mathlib.AddCommGroup.exact

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

def tweak (c : ℝ≥0ᵒᵖ) (n : ℕ) :
  ((unop.{u+2} ((FPsystem.{u} r' BD κ M).op.obj (r'.MulLeft.op.obj c))).X n).as ≅
  (FiltrationPow.{u} r' (r' * (unop.{1} c * κ n)) (BD.X n)).obj M :=
begin
  dsimp [FPsystem, FPsystem.X, nnreal.MulLeft],
  haveI : fact (r' * unop.{1} c * κ n ≤ r' * (unop.{1} c * κ n)) := ⟨(mul_assoc _ _ _).le⟩,
  haveI : fact (r' * (unop.{1} c * κ n) ≤ r' * unop.{1} c * κ n) := ⟨(mul_assoc _ _ _).ge⟩,
  refine ⟨Filtration.cast_le.{u} _ _ _, Filtration.cast_le.{u} _ _ _, _, _⟩,
  tidy,
end

def Tinv : aux_system r' BD κ M V ⟶ (ScaleIndexLeft r').obj (aux_system r' BD κ M V) :=
@whisker_right _ _ _ _ _ _ (FPsystem r' BD κ M).op ((nnreal.MulLeft r').op ⋙ (FPsystem r' BD κ M).op)
  (nat_trans.op $ FPsystem.Tinv r' BD κ M)
  ((((CLC.{v u} V).right_op.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _).op ⋙
    homological_complex.unop_functor)

-- lemma Tinv_eq (c : ℝ≥0ᵒᵖ) (n : ℕ) : ((Tinv r' BD κ M V).app c).f n =
--   _ ≫ (CLCFP.Tinv V r' _ _ (BD.X n)).app (op M) ≫ _ :=
-- begin
--   sorry
-- end

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
.

variables [normed_with_aut r V]

-- lemma T_inv_eq (c : ℝ≥0ᵒᵖ) (n : ℕ) : ((T_inv r r' BD κ M V).app c).f n =
--   (CLC V).map _ ≫
--   (CLC.T_inv r V).app (op.{u+2} (pseudo_normed_group.filtration_obj.{u} (↥M ^ BD.X n) (r' * (unop c * κ n))))
--   ≫ (CLC V).map _ :=
-- begin
--   sorry
-- end

def res : aux_system r' BD κ M V ⟶ (ScaleIndexLeft r').obj (aux_system r' BD κ M V) :=
@whisker_right _ _ _ _ _ _ (FPsystem r' BD κ M).op ((nnreal.MulLeft r').op ⋙ (FPsystem r' BD κ M).op)
  (nat_trans.op $ FPsystem.res r' BD κ M)
  ((((CLC.{v u} V).right_op.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _).op ⋙
    homological_complex.unop_functor)


def Tinv2 :
  aux_system r' BD κ M V ⟶ (ScaleIndexLeft r').obj (aux_system r' BD κ M V) :=
Tinv r' BD κ M V - T_inv r r' BD κ M V ≫ res r' BD κ M V
.

lemma aux_system_d_eq (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  arrow.mk (((aux_system r' BD κ M V).obj c).d i (i + 1)) =
  arrow.mk ((universal_map.eval_CLCFP V r' (unop c * κ i) (unop c * κ (i + 1)) (BD.d (i + 1) i) : _).app (op M)) :=
begin
  dsimp [aux_system, FPsystem],
  rw [chain_complex.of_d],
  dsimp [FreeAb.eval, functor.map_FreeAb, functor.right_op_map, FPsystem.d,
    universal_map.eval_FP2, universal_map.eval_CLCFP, universal_map.eval_LCFP],
  simp only [nat_trans.app_sum, map_sum, ← normed_group_hom_completion_hom_apply,
    category_theory.unop_sum],
  congr' 1,
  refine finset.sum_congr rfl _,
  rintro ⟨g, hg⟩ -,
  simp only [nat_trans.app_zsmul, map_zsmul, category_theory.unop_zsmul],
  dsimp only [basic_universal_map.eval_FP2, basic_universal_map.eval_LCFP,
    whisker_right_app, nat_trans.op_app, unop_op, FreeAb.of_functor,
    free_abelian_group.map_of_apply],
  rw [free_abelian_group.lift.of],
  refl,
end

def incl_f (c : ℝ≥0ᵒᵖ) (n : ℕ) :
  ((BD.complex κ r V r' (unop c)).obj (op M)).X n ⟶ ((aux_system r' BD κ M V).obj c).X n :=
begin
  dsimp [breen_deligne.data.complex, breen_deligne.data.complex₂, breen_deligne.data.complex₂_X,
    CLCTinv, aux_system, FPsystem, FPsystem.X, functor.map_FreeAb, FreeAb.eval],
  exact (SemiNormedGroup.equalizer.ι _ _ : _),
end

lemma incl_comm (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  incl_f.{u v} r r' BD κ M V c i ≫ ((aux_system.{u v} r' BD κ M V).obj c).d i (i + 1) =
  ((BD.complex κ r V r' (unop c)).obj (op.{u+2} M)).d i (i + 1) ≫ incl_f.{u v} r r' BD κ M V c (i + 1) :=
begin
  dsimp [aux_system],
  erw [chain_complex.of_d, breen_deligne.data.complex_obj_d],
  dsimp [breen_deligne.data.complex, breen_deligne.data.complex₂, breen_deligne.data.complex₂_X,
    CLCTinv, FPsystem, FPsystem.X, functor.map_FreeAb, FreeAb.eval,
    universal_map.eval_CLCFPTinv, universal_map.eval_CLCFPTinv₂,
    SemiNormedGroup.equalizer.map_nat, incl_f],
  delta id, dsimp only [], symmetry,
  convert SemiNormedGroup.equalizer.map_comp_ι _ _ _ _ using 2,
  apply arrow.mk_injective,
  rw ← aux_system_d_eq,
  dsimp [aux_system],
  erw [chain_complex.of_d],
  refl,
end

def incl (c : ℝ≥0ᵒᵖ) : (BD.complex κ r V r' (unop c)).obj (op M) ⟶ (aux_system r' BD κ M V).obj c :=
{ f := incl_f r r' BD κ M V c,
  comm' := by { rintro i j (rfl : i + 1 = j), apply incl_comm } }

def incl' (c : ℝ≥0ᵒᵖ) :=
(functor.map_homological_complex (forget₂ _ Ab) _).map (incl r r' BD κ M V c)

def Tinv2' (c : ℝ≥0ᵒᵖ) :=
(functor.map_homological_complex (forget₂ _ Ab) _).map ((Tinv2 r r' BD κ M V).app c)

lemma _root_.SemiNormedGroup.equalizer.ι_injective {V W : SemiNormedGroup} (f g : V ⟶ W) :
  function.injective (SemiNormedGroup.equalizer.ι f g) :=
subtype.val_injective

lemma _root_.SemiNormedGroup.equalizer.forget₂_ι {V W : SemiNormedGroup} (f g : V ⟶ W) :
  (forget₂ _ Ab).map (SemiNormedGroup.equalizer.ι f g) =
  add_subgroup.subtype (add_monoid_hom.ker ((forget₂ _ Ab).map (f - g))) :=
rfl

lemma short_exact (c : ℝ≥0ᵒᵖ) (n : ℕ) :
  short_exact ((incl' r r' BD κ M V c).f n) ((Tinv2' r r' BD κ M V c).f n) :=
begin
  apply_with @short_exact.mk {instances := ff},
  { rw AddCommGroup.mono_iff_injective,
    dsimp [incl', incl, incl_f,
      breen_deligne.data.complex, breen_deligne.data.complex₂, breen_deligne.data.complex₂_X],
    exact SemiNormedGroup.equalizer.ι_injective _ _, },
  { rw AddCommGroup.epi_iff_surjective,
    sorry },
  { rw AddCommGroup.exact_iff,
    dsimp [incl', incl, incl_f, Tinv2',
      breen_deligne.data.complex, breen_deligne.data.complex₂, breen_deligne.data.complex₂_X],
    rw [SemiNormedGroup.equalizer.forget₂_ι, add_subgroup.subtype_range],
    sorry }
end

end aux_system
