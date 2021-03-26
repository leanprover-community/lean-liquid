import pseudo_normed_group.LC

open_locale classical nnreal
noncomputable theory
local attribute [instance] type_pow

open NormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group

universe variable u
variables (r : ℝ≥0) (V : NormedGroup) (r' : ℝ≥0)
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)

/-- The "functor" that sends `M` and `c` to `V-hat((filtration M c)^n)` -/
def CLCP (V : NormedGroup) (n : ℕ) : Profiniteᵒᵖ ⥤ NormedGroup :=
LCP V n ⋙ Completion

/-- The "functor" that sends `M` and `c` to `V-hat((filtration M c)^n)` -/
def CLCFP (V : NormedGroup) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ NormedGroup :=
(ProFiltPseuNormGrpWithTinv.level r' c).op ⋙ CLCP V n

theorem CLCFP_def (V : NormedGroup) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  CLCFP V r' c n = LCFP V r' c n ⋙ Completion := rfl

namespace CLCFP

lemma map_norm_noninc {M₁ M₂} (f : M₁ ⟶ M₂) :
  ((CLCFP V r' c n).map f).norm_noninc :=
Completion_map_norm_noninc _ $ LCFP.map_norm_noninc _ _ _ _ _

@[simps app]
def res [fact (c₂ ≤ c₁)] : CLCFP V r' c₁ n ⟶ CLCFP V r' c₂ n :=
(whisker_right (LCFP.res V r' c₁ c₂ n) Completion : _)

lemma res_app' [fact (c₂ ≤ c₁)] (M) :
  (res V r' c₁ c₂ n).app M =
    (CLCP V n).map (Filtration.cast_le (unop M : ProFiltPseuNormGrpWithTinv r') c₂ c₁).op :=
rfl

@[simp] lemma res_refl : res V r' c c n = 𝟙 _ :=
by { simp only [res, LCFP.res_refl, whisker_right_id'], refl }

lemma res_comp_res [fact (c₂ ≤ c₁)] [fact (c₃ ≤ c₂)] [fact (c₃ ≤ c₁)] :
  res V r' c₁ c₂ n ≫ res V r' c₂ c₃ n = res V r' c₁ c₃ n :=
by simp only [res, ← whisker_right_comp, LCFP.res_comp_res]

lemma res_norm_noninc [fact (c₂ ≤ c₁)] (M) :
  ((res V r' c₁ c₂ n).app M).norm_noninc :=
Completion_map_norm_noninc _ $ LCFP.res_norm_noninc _ _ _ _ _ _

section Tinv
open profinitely_filtered_pseudo_normed_group_with_Tinv
variables [fact (0 < r')]

@[simps {fully_applied := ff}]
def Tinv [fact (c₂ ≤ r' * c₁)] : CLCFP V r' c₁ n ⟶ CLCFP V r' c₂ n :=
(whisker_right (nat_trans.op $ FiltrationPow.Tinv r' c₂ c₁ n)
  (LocallyConstant.obj V ⋙ Completion) : _)
.

lemma Tinv_def [fact (c₂ ≤ r' * c₁)] : Tinv V r' c₁ c₂ n =
  (whisker_right (LCFP.Tinv V r' c₁ c₂ n) Completion : _) := rfl

lemma res_comp_Tinv [fact (c₂ ≤ c₁)] [fact (c₃ ≤ c₂)] [fact (c₂ ≤ r' * c₁)] [fact (c₃ ≤ r' * c₂)] :
  res V r' c₁ c₂ n ≫ Tinv V r' c₂ c₃ n = Tinv V r' c₁ c₂ n ≫ res V r' c₂ c₃ n :=
begin
  simp only [Tinv, res, LCFP.res, whisker_right_twice, ← whisker_right_comp, ← nat_trans.op_comp],
  refl
end

end Tinv

section T_inv

variables [normed_with_aut r V] [fact (0 < r)]

def T_inv' : CLCP V n ⟶ CLCP V n :=
(whisker_right (LCFP.T_inv' r V n) Completion : _)

@[simps app_apply {fully_applied := ff}]
def T_inv : CLCFP V r' c n ⟶ CLCFP V r' c n :=
(whisker_left _ (T_inv' r V n) : _)
.

lemma T_inv_def : T_inv r V r' c n = (whisker_right (LCFP.T_inv r V r' c n) Completion : _) :=
rfl

lemma T_inv_app [fact (0 < r)] (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :
  (T_inv r V r' c n).app M =
    (T_inv' r V n).app ((ProFiltPseuNormGrpWithTinv.level r' c).op.obj M) :=
rfl

lemma res_comp_T_inv [fact (c₂ ≤ c₁)] :
  res V r' c₁ c₂ n ≫ T_inv r V r' c₂ n =
    T_inv r V r' c₁ n ≫ res V r' c₁ c₂ n :=
begin
  ext M : 2,
  simp only [nat_trans.comp_app, res_app', T_inv_app],
  exact (T_inv' r V n).naturality _,
end

end T_inv

end CLCFP

namespace breen_deligne

open CLCFP
variables {l m n}

-- namespace basic_universal_map

-- variables (ϕ : basic_universal_map m n)

-- @[simps]
-- def eval_CLCFP : CLCFP V r' c₂ n ⟶ CLCFP V r' c₁ m :=
-- Completion.map (ϕ.eval_LCFP V r' c₁ c₂)

-- lemma map_comp_eval_CLCFP [ϕ.suitable c₁ c₂] :
--   map V r' c₂ n f ≫ ϕ.eval_CLCFP V r' c₁ c₂ = ϕ.eval_CLCFP V r' c₁ c₂ ≫ map V r' c₁ m f :=
-- by simp only [map, eval_CLCFP, ← category_theory.functor.map_comp, ← op_comp, map_comp_eval_LCFP]

-- lemma res_comp_eval_CLCFP
--   [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
--   res V r' c₃ c₄ n ≫ ϕ.eval_CLCFP V r' c₁ c₃ =
--     ϕ.eval_CLCFP V r' c₂ c₄ ≫ res V r' c₁ c₂ m :=
-- by simp only [res, eval_CLCFP, ← category_theory.functor.map_comp, ← op_comp,
--   res_comp_eval_LCFP V r' _ c₁ c₂ c₃ c₄]

-- lemma Tinv_comp_eval_CLCFP [fact (0 < r')] [ϕ.suitable c₁ c₂] :
--   Tinv V r' c₂ n ≫ ϕ.eval_CLCFP V r' (r' * c₁) (r' * c₂) =
--     ϕ.eval_CLCFP V r' c₁ c₂ ≫ Tinv V r' c₁ m :=
-- by simp only [Tinv, eval_CLCFP, ← category_theory.functor.map_comp, ← op_comp,
--   Tinv_comp_eval_LCFP V r' _ c₁ c₂]

-- lemma T_inv_comp_eval_CLCFP [normed_with_aut r V] [fact (0 < r)] [ϕ.suitable c₁ c₂] :
--   T_inv r V r' c₂ n ≫ ϕ.eval_CLCFP V r' c₁ c₂ =
--     ϕ.eval_CLCFP V r' c₁ c₂ ≫ T_inv r V r' c₁ m :=
-- by simp only [T_inv, eval_CLCFP, ← category_theory.functor.map_comp, ← op_comp,
--   T_inv_comp_eval_LCFP r V r' c₁ c₂]

-- end basic_universal_map

namespace universal_map

variables (ϕ : universal_map m n)

def eval_CLCFP : CLCFP V r' c₁ n ⟶ CLCFP V r' c₂ m :=
(whisker_right (ϕ.eval_LCFP V r' c₁ c₂) Completion : _)

@[simp] lemma eval_CLCFP_zero :
  (0 : universal_map m n).eval_CLCFP V r' c₁ c₂ = 0 :=
begin
  simp only [eval_CLCFP, eval_LCFP_zero],
  ext x : 2,
  exact Completion.map_zero _ _
end

open category_theory.limits

lemma eval_CLCFP_comp (g : universal_map m n) (f : universal_map l m)
  [hg : g.suitable c₂ c₁] [hf : f.suitable c₃ c₂] :
  (comp g f).eval_CLCFP V r' c₁ c₃ =
    g.eval_CLCFP V r' c₁ c₂ ≫ f.eval_CLCFP V r' c₂ c₃ :=
by simp only [eval_CLCFP, ← whisker_right_comp, eval_LCFP_comp V r' c₁ c₂ c₃]

lemma res_comp_eval_CLCFP
  [fact (c₂ ≤ c₁)] [ϕ.suitable c₄ c₂] [ϕ.suitable c₃ c₁] [fact (c₄ ≤ c₃)] :
  res V r' c₁ c₂ n ≫ ϕ.eval_CLCFP V r' c₂ c₄ =
    ϕ.eval_CLCFP V r' c₁ c₃ ≫ res V r' c₃ c₄ m :=
by simp only [eval_CLCFP, res, ← whisker_right_comp]; congr' 1; apply res_comp_eval_LCFP

lemma Tinv_comp_eval_CLCFP [fact (0 < r')] [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [ϕ.suitable c₃ c₁] [ϕ.suitable c₄ c₂] :
  Tinv V r' c₁ c₂ n ≫ ϕ.eval_CLCFP V r' c₂ c₄ =
    ϕ.eval_CLCFP V r' c₁ c₃ ≫ Tinv V r' c₃ c₄ m :=
by simp only [eval_CLCFP, Tinv_def, ← whisker_right_comp]; congr' 1; apply Tinv_comp_eval_LCFP

lemma T_inv_comp_eval_CLCFP [normed_with_aut r V] [fact (0 < r)] [ϕ.suitable c₂ c₁] :
  T_inv r V r' c₁ n ≫ ϕ.eval_CLCFP V r' c₁ c₂ =
    ϕ.eval_CLCFP V r' c₁ c₂ ≫ T_inv r V r' c₂ m :=
by simp only [eval_CLCFP, T_inv_def, ← whisker_right_comp, T_inv_comp_eval_LCFP]

end universal_map

end breen_deligne
