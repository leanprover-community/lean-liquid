import for_mathlib.homological_complex_op
import for_mathlib.split_exact
import for_mathlib.AddCommGroup.exact

import pseudo_normed_group.FP2
import pseudo_normed_group.system_of_complexes

import system_of_complexes.rescale

import prop_92.prop_92

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
variables (BD : breen_deligne.data)
variables (M : ProFiltPseuNormGrpWithTinv.{u} r')
variables (V : SemiNormedGroup.{v})

set_option pp.universes true

def aux_system (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.suitable (κ c)] [∀ (n : ℕ), fact (monotone (function.swap κ n))] :
  system_of_complexes :=
(FPsystem r' BD M κ).op ⋙
  (((CLC.{v u} V).right_op.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _).op ⋙
  homological_complex.unop_functor

namespace aux_system

variables [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)]

open system_of_complexes opposite

-- def tweak (c : ℝ≥0ᵒᵖ) (n : ℕ) :
--   ((unop.{u+2} ((FPsystem.{u} r' BD M κ).op.obj (r'.MulLeft.op.obj c))).X n).as ≅
--   (FiltrationPow.{u} r' (r' * (unop.{1} c * κ n)) (BD.X n)).obj M :=
-- begin
--   dsimp [FPsystem, FPsystem.X, nnreal.MulLeft],
--   haveI : fact (r' * unop.{1} c * κ n ≤ r' * (unop.{1} c * κ n)) := ⟨(mul_assoc _ _ _).le⟩,
--   haveI : fact (r' * (unop.{1} c * κ n) ≤ r' * unop.{1} c * κ n) := ⟨(mul_assoc _ _ _).ge⟩,
--   refine ⟨Filtration.cast_le.{u} _ _ _, Filtration.cast_le.{u} _ _ _, _, _⟩,
--   tidy,
-- end

variables (κ₁ κ₂ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.suitable (κ₁ c)] [∀ c, BD.suitable (κ₂ c)]

def Tinv [hκ₁ : ∀ n, fact (monotone (function.swap κ₁ n))] [hκ₂ : ∀ n, fact (monotone (function.swap κ₂ n))]
  [∀ c n, fact (κ₁ c n ≤ r' * κ₂ c n)] :
  aux_system r' BD M V κ₂ ⟶ aux_system r' BD M V κ₁ :=
whisker_right (nat_trans.op $ FPsystem.Tinv r' BD M κ₁ κ₂)
  ((((CLC.{v u} V).right_op.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _).op ⋙
    homological_complex.unop_functor)

lemma Tinv_eq [hκ₁ : ∀ n, fact (monotone (function.swap κ₁ n))] [hκ₂ : ∀ n, fact (monotone (function.swap κ₂ n))]
  [∀ c n, fact (κ₁ c n ≤ r' * κ₂ c n)] (c : ℝ≥0ᵒᵖ) (n : ℕ) :
  ((Tinv r' BD M V κ₁ κ₂).app c).f n =
  ((CLCFP.Tinv V r' _ _ (BD.X n)).app (op M) : _) :=
begin
  dsimp only [Tinv, CLCFP.Tinv, FPsystem.Tinv, FP2.Tinv,
    homological_complex.comp_f, aux_system, functor.comp_map, homological_complex.unop_functor,
    homological_complex.unop_d, functor.op_obj, functor.map_homological_complex_obj_d,
    unop_op, CLC, functor.op_map, quiver.hom.unop_op, functor.map_homological_complex_map_f,
    functor.map_FreeAb, FreeAb.eval, free_abelian_group.map_of_apply,
    FPsystem, FP2.res_app, FreeAb.of_functor, functor.right_op_map,
    whisker_right_app, nat_trans.op_app],
  erw [free_abelian_group.lift.of],
  refl,
end

def T_inv [normed_with_aut r V]
  (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.suitable (κ c)] [∀ (n : ℕ), fact (monotone (function.swap κ n))] :
  aux_system r' BD M V κ ⟶ aux_system r' BD M V κ :=
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

lemma T_inv_eq
  (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.suitable (κ c)] [∀ (n : ℕ), fact (monotone (function.swap κ n))]
  (c : ℝ≥0ᵒᵖ) (n : ℕ) : ((T_inv r r' BD M V κ).app c).f n =
  ((CLCFP.T_inv r V r' _ (BD.X n)).app (op M) : _) :=
begin
  dsimp only [T_inv, CLCFP.T_inv, FPsystem, chain_complex.of_X, FPsystem.X,
    homological_complex.comp_f, aux_system, functor.comp_map, homological_complex.unop_functor,
    homological_complex.unop_d, functor.op_obj, functor.map_homological_complex_obj_d,
    functor.map_homological_complex_map_f, functor.map_FreeAb,
    unop_op, CLC, functor.op_map, functor.op_obj, quiver.hom.unop_op,
    FreeAb.eval, free_abelian_group.map_of_apply, FPsystem, FP2.res_app, FreeAb.of_functor,
    functor.right_op_map, whisker_right_app, nat_trans.op_app, whisker_left_app],
  refl,
end

def res [hκ₁ : ∀ n, fact (monotone (function.swap κ₁ n))] [hκ₂ : ∀ n, fact (monotone (function.swap κ₂ n))]
  [∀ c n, fact (κ₁ c n ≤ κ₂ c n)] :
  aux_system r' BD M V κ₂ ⟶ aux_system r' BD M V κ₁ :=
whisker_right (nat_trans.op $ FPsystem.res r' BD M κ₁ κ₂)
  ((((CLC.{v u} V).right_op.map_FreeAb ⋙ FreeAb.eval _).map_homological_complex _).op ⋙
    homological_complex.unop_functor)

lemma res_eq [hκ₁ : ∀ n, fact (monotone (function.swap κ₁ n))] [hκ₂ : ∀ n, fact (monotone (function.swap κ₂ n))]
  [∀ c n, fact (κ₁ c n ≤ r' * κ₂ c n)] [∀ c n, fact (κ₁ c n ≤ κ₂ c n)] (c : ℝ≥0ᵒᵖ) (n : ℕ) :
  ((res r' BD M V κ₁ κ₂).app c).f n =
  ((CLCFP.res V r' _ _ (BD.X n)).app (op M) : _) :=
begin
  dsimp only [res, CLCFP.res, FPsystem.res, FP2.res,
    homological_complex.comp_f, aux_system, functor.comp_map, homological_complex.unop_functor,
    homological_complex.unop_d, functor.op_obj, functor.map_homological_complex_obj_d,
    unop_op, CLC, functor.op_map, quiver.hom.unop_op, functor.map_homological_complex_map_f,
    functor.map_FreeAb, FreeAb.eval, free_abelian_group.map_of_apply,
    FPsystem, FP2.res_app, FreeAb.of_functor, functor.right_op_map,
    whisker_right_app, nat_trans.op_app],
  rw [free_abelian_group.lift.of],
  refl,
end

def Tinv2 [hκ₁ : ∀ n, fact (monotone (function.swap κ₁ n))] [hκ₂ : ∀ n, fact (monotone (function.swap κ₂ n))]
  [∀ c n, fact (κ₁ c n ≤ r' * κ₂ c n)] [∀ c n, fact (κ₁ c n ≤ κ₂ c n)] :
  aux_system r' BD M V κ₂ ⟶ aux_system r' BD M V κ₁ :=
Tinv r' BD M V κ₁ κ₂ - T_inv r r' BD M V κ₂ ≫ res r' BD M V κ₁ κ₂
.

lemma Tinv2_eq [hκ₁ : ∀ n, fact (monotone (function.swap κ₁ n))] [hκ₂ : ∀ n, fact (monotone (function.swap κ₂ n))]
  [∀ c n, fact (κ₁ c n ≤ r' * κ₂ c n)] [∀ c n, fact (κ₁ c n ≤ κ₂ c n)] (c : ℝ≥0ᵒᵖ) (n : ℕ) :
  ((Tinv2 r r' BD M V κ₁ κ₂).app c).f n =
  ((CLCFP.Tinv V r' _ _ (BD.X n)).app (op M) : _) -
  ((CLCFP.T_inv r V r' _ (BD.X n)).app (op M) : _) ≫ ((CLCFP.res V r' _ _ (BD.X n)).app (op M) : _) :=
by rw [Tinv2, nat_trans.app_sub, homological_complex.sub_f_apply, Tinv_eq,
    nat_trans.comp_app, homological_complex.comp_f, T_inv_eq, res_eq]

lemma aux_system_d_eq
  (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.suitable (κ c)] [∀ (n : ℕ), fact (monotone (function.swap κ n))]
  (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  arrow.mk (((aux_system r' BD M V κ).obj c).d i (i + 1)) =
  arrow.mk ((universal_map.eval_CLCFP V r' (κ (unop c) i) (κ (unop c) (i + 1)) (BD.d (i + 1) i) : _).app (op M)) :=
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

section

variables (κ : ℕ → ℝ≥0) [BD.suitable κ]

instance mul_left_mono (n : ℕ) :
  fact (monotone (function.swap (λ (c : ℝ≥0) (n : ℕ), c * κ n) n)) :=
⟨λ c₁ c₂ h, mul_le_mul' h le_rfl⟩

def incl_f (c : ℝ≥0ᵒᵖ) (n : ℕ) :
  ((BD.complex κ r V r' (unop c)).obj (op M)).X n ⟶ ((aux_system r' BD M V (λ c n, c * κ n)).obj c).X n :=
begin
  dsimp [breen_deligne.data.complex, breen_deligne.data.complex₂, breen_deligne.data.complex₂_X,
    CLCTinv, aux_system, FPsystem, FPsystem.X, functor.map_FreeAb, FreeAb.eval],
  exact (SemiNormedGroup.equalizer.ι _ _ : _),
end

lemma incl_comm (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  incl_f.{u v} r r' BD M V κ c i ≫ ((aux_system.{u v} r' BD M V (λ c n, c * κ n)).obj c).d i (i + 1) =
  ((BD.complex κ r V r' (unop c)).obj (op.{u+2} M)).d i (i + 1) ≫ incl_f.{u v} r r' BD M V κ c (i + 1) :=
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
  rw ← aux_system_d_eq r' BD M V (λ c n, c * κ n),
  dsimp [aux_system],
  erw [chain_complex.of_d],
  refl,
end

def incl : (BD.system κ r V r').obj (op M) ⟶ aux_system r' BD M V (λ c n, c * κ n) :=
{ app := λ c,
  { f := incl_f r r' BD M V κ c,
    comm' := by { rintro i j (rfl : i + 1 = j), apply incl_comm } },
  naturality' := sorry }

def incl' := whisker_right (incl r r' BD M V κ) (functor.map_homological_complex (forget₂ _ Ab.{max u v}) _)

end

def Tinv2' [hκ₁ : ∀ n, fact (monotone (function.swap κ₁ n))] [hκ₂ : ∀ n, fact (monotone (function.swap κ₂ n))]
  [∀ c n, fact (κ₁ c n ≤ r' * κ₂ c n)] [∀ c n, fact (κ₁ c n ≤ κ₂ c n)] :=
whisker_right (Tinv2 r r' BD M V κ₁ κ₂)
(functor.map_homological_complex (forget₂ _ Ab.{max u v}) _)

lemma _root_.SemiNormedGroup.equalizer.ι_injective {V W : SemiNormedGroup} (f g : V ⟶ W) :
  function.injective (SemiNormedGroup.equalizer.ι f g) :=
subtype.val_injective

lemma _root_.SemiNormedGroup.equalizer.forget₂_ι {V W : SemiNormedGroup} (f g : V ⟶ W) :
  (forget₂ _ Ab).map (SemiNormedGroup.equalizer.ι f g) =
  add_subgroup.subtype (add_monoid_hom.ker ((forget₂ _ Ab).map (f - g))) :=
rfl

instance mul_left_mono' (κ : ℕ → ℝ≥0) (n : ℕ) :
  fact (monotone (function.swap (λ (c : ℝ≥0) (n : ℕ), r' * (c * κ n)) n)) :=
⟨λ c₁ c₂ h, mul_le_mul' le_rfl $ mul_le_mul' h le_rfl⟩

lemma neg_surjective {A B : Ab} (f : A ⟶ B) (hf : function.surjective f) :
  function.surjective (-f) :=
begin
  intro y, obtain ⟨x, rfl⟩ := hf y, use -x, simp only [pi.neg_apply, map_neg, neg_neg],
end

lemma short_exact [fact (r < 1)] (κ : ℕ → ℝ≥0) [BD.suitable κ]
  [∀ c n, fact (κ₁ c n ≤ r' * (c * κ n))] (c : ℝ≥0ᵒᵖ) (n : ℕ) :
  short_exact (((incl' r r' BD M V κ).app c).f n)
    (((Tinv2' r r' BD M V (λ c n, r' * (c * κ n)) (λ c n, c * κ n)).app c).f n) :=
begin
  apply_with @short_exact.mk {instances := ff},
  { rw AddCommGroup.mono_iff_injective,
    dsimp [incl', incl, incl_f,
      breen_deligne.data.complex, breen_deligne.data.complex₂, breen_deligne.data.complex₂_X],
    exact SemiNormedGroup.equalizer.ι_injective _ _, },
  { rw [Tinv2', whisker_right_app, functor.map_homological_complex_map_f, Tinv2_eq,
      ← nat_trans.comp_app, ← CLCFP.res_comp_T_inv, nat_trans.comp_app,
      ← neg_sub, functor.map_neg, functor.map_sub, category_theory.functor.map_comp,
      AddCommGroup.epi_iff_surjective],
    apply neg_surjective,
    have := CLCFP.T_inv_sub_Tinv_surjective r r' V (unop c * κ n) (BD.X n) (op M),
    rw [CLCFP.T_inv_sub_Tinv, nat_trans.app_sub, nat_trans.comp_app] at this,
    exact this, },
  { rw AddCommGroup.exact_iff,
    dsimp [incl', incl, incl_f, Tinv2',
      breen_deligne.data.complex, breen_deligne.data.complex₂, breen_deligne.data.complex₂_X],
    rw [SemiNormedGroup.equalizer.forget₂_ι, add_subgroup.subtype_range, Tinv2_eq,
      ← nat_trans.comp_app, ← CLCFP.res_comp_T_inv],
    refl, }
end

end aux_system
