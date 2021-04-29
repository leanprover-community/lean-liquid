import pseudo_normed_group.LC
/-!

# V-hat(M_c^n)

One of the key players in the proof of the main theorem of this repo is
the normed group V-hat(M-bar_r'(S)_{≤c}^n). This file constructs

## Key defintions

- `CLCP V n`: the functor that sends a profinite set `S` to `V-hat(S^n)`
- `CLFCP v r' c n`: the functor sending a profinitely-filtered `T⁻¹`-module `M`
   to `V-hat((M_c)^n)`

-/
open_locale classical nnreal
noncomputable theory
local attribute [instance] type_pow

open NormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group

universe variable u
variables (r : ℝ≥0) (V : NormedGroup) (r' : ℝ≥0)
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)

/-- `CLC V n` is the functor that sends a profinite set `S` to `V-hat(S^n)` -/
def CLC (V : NormedGroup) : Profiniteᵒᵖ ⥤ NormedGroup :=
LC V ⋙ Completion

namespace CLC

lemma map_norm_noninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((CLC V).map f).norm_noninc :=
Completion_map_norm_noninc _ $ LC.map_norm_noninc _ _

def T [normed_with_aut r V] [fact (0 < r)] : CLC V ≅ CLC V :=
((whiskering_right _ _ _).obj _).map_iso (LC.T r V)

lemma T_bound_by [normed_with_aut r V] [fact (0 < r)] (A) :
  ((T r V).hom.app A).bound_by r :=
Completion_map_bound_by _ _ $ LC.T_bound_by _ _ _

def T_inv [normed_with_aut r V] [fact (0 < r)] : CLC V ⟶ CLC V :=
whisker_right (LC.T_inv r V) Completion

lemma T_inv_eq [normed_with_aut r V] [fact (0 < r)] : (T r V).inv = T_inv r V := rfl

end CLC

/-- `CLFCP v r' c n` is the functor sending a profinitely-filtered `T⁻¹`-module `M`
   to `V-hat((M_c)^n)` -/
def CLCFP (V : NormedGroup) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ NormedGroup :=
(FiltrationPow r' c n).op ⋙ CLC V

theorem CLCFP_def (V : NormedGroup) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  CLCFP V r' c n = LCFP V r' c n ⋙ Completion := rfl

namespace CLCFP

lemma map_norm_noninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((CLCFP V r' c n).map f).norm_noninc :=
CLC.map_norm_noninc _ _

@[simps app]
def res [fact (c₂ ≤ c₁)] : CLCFP V r' c₁ n ⟶ CLCFP V r' c₂ n :=
(whisker_right (nat_trans.op $ FiltrationPow.cast_le r' c₂ c₁ n) (CLC V) : _)

lemma res_def [fact (c₂ ≤ c₁)] :
  res V r' c₁ c₂ n = whisker_right (nat_trans.op (FiltrationPow.cast_le r' c₂ c₁ n)) (CLC V) :=
rfl

lemma res_def' [fact (c₂ ≤ c₁)] (M : ProFiltPseuNormGrpWithTinv r') :
  (res V r' c₁ c₂ n).app (op M) =
  (CLC V).map ((Pow n).map $ (Filtration.cast_le M c₂ c₁)).op :=
rfl

lemma res_app' [fact (c₂ ≤ c₁)] (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :
  (res V r' c₁ c₂ n).app M = (CLC V).map ((FiltrationPow.cast_le r' c₂ c₁ n).app (unop M)).op :=
rfl

@[simp] lemma res_refl : res V r' c c n = 𝟙 _ :=
by { rw [res, FiltrationPow.cast_le_refl, nat_trans.op_id, whisker_right_id'], refl }

lemma res_comp_res [fact (c₂ ≤ c₁)] [fact (c₃ ≤ c₂)] [fact (c₃ ≤ c₁)] :
  res V r' c₁ c₂ n ≫ res V r' c₂ c₃ n = res V r' c₁ c₃ n :=
by simp only [res, ← whisker_right_comp, FiltrationPow.cast_le_comp, ← nat_trans.op_comp]

lemma res_norm_noninc [fact (c₂ ≤ c₁)] (M) :
  ((res V r' c₁ c₂ n).app M).norm_noninc :=
Completion_map_norm_noninc _ $ LCFP.res_norm_noninc _ _ _ _ _ _

section Tinv
-- kmb commented out the next line
--open profinitely_filtered_pseudo_normed_group_with_Tinv
variables [fact (0 < r')] [fact (c₂ ≤ r' * c₁)]

-- @[simps obj {fully_applied := ff}]
def Tinv : CLCFP V r' c₁ n ⟶ CLCFP V r' c₂ n :=
(whisker_right (nat_trans.op $ FiltrationPow.Tinv r' c₂ c₁ n)
  (LocallyConstant.obj V ⋙ Completion) : _)
.

lemma Tinv_def : Tinv V r' c₁ c₂ n =
  (whisker_right (LCFP.Tinv V r' c₁ c₂ n) Completion : _) := rfl

lemma Tinv_def' : Tinv V r' c₁ c₂ n =
  whisker_right (nat_trans.op $ FiltrationPow.Tinv r' c₂ c₁ n) (CLC V) := rfl

lemma res_comp_Tinv [fact (c₂ ≤ c₁)] [fact (c₃ ≤ c₂)] [fact (c₃ ≤ r' * c₂)] :
  res V r' c₁ c₂ n ≫ Tinv V r' c₂ c₃ n = Tinv V r' c₁ c₂ n ≫ res V r' c₂ c₃ n :=
begin
  dsimp only [Tinv, res, CLC, LC],
  simp only [← whisker_right_comp, ← nat_trans.op_comp],
  refl
end

end Tinv

section T_inv

variables [normed_with_aut r V] [fact (0 < r)]

@[simps {fully_applied := ff}]
def T : CLCFP V r' c n ≅ CLCFP V r' c n :=
((whiskering_left _ _ _).obj (FiltrationPow r' c n).op).map_iso (CLC.T r V)

@[simps app_apply {fully_applied := ff}]
def T_inv : CLCFP V r' c n ⟶ CLCFP V r' c n :=
whisker_left (FiltrationPow r' c n).op (CLC.T_inv r V)

lemma T_inv_eq [normed_with_aut r V] [fact (0 < r)] : (T r V r' c n).inv = T_inv r V r' c n := rfl

lemma T_inv_def : T_inv r V r' c n = (whisker_right (LCFP.T_inv r V r' c n) Completion : _) :=
rfl

lemma T_inv_app [fact (0 < r)] (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :
  (T_inv r V r' c n).app M =
    (CLC.T_inv r V).app ((FiltrationPow r' c n).op.obj M) :=
rfl

lemma res_comp_T_inv [fact (c₂ ≤ c₁)] :
  res V r' c₁ c₂ n ≫ T_inv r V r' c₂ n =
    T_inv r V r' c₁ n ≫ res V r' c₁ c₂ n :=
begin
  ext M : 2,
  simp only [nat_trans.comp_app, res_app', T_inv_app],
  exact (CLC.T_inv r V).naturality _,
end

end T_inv

end CLCFP

namespace breen_deligne

open CLCFP
variables {l m n}

namespace universal_map

variables (ϕ ψ : universal_map m n)

def eval_CLCFP [ϕ.suitable c₂ c₁] : CLCFP V r' c₁ n ⟶ CLCFP V r' c₂ m :=
(whisker_right (ϕ.eval_LCFP V r' c₁ c₂) Completion : _)

@[simp] lemma eval_CLCFP_zero :
  (0 : universal_map m n).eval_CLCFP V r' c₁ c₂ = 0 :=
begin
  simp only [eval_CLCFP, eval_LCFP_zero],
  ext x : 2,
  exact Completion.map_zero _ _
end

@[simp] lemma eval_CLCFP_add [ϕ.suitable c₂ c₁] [ψ.suitable c₂ c₁] :
  (ϕ + ψ : universal_map m n).eval_CLCFP V r' c₁ c₂ =
  ϕ.eval_CLCFP V r' c₁ c₂ + ψ.eval_CLCFP V r' c₁ c₂ :=
begin
  simp only [eval_CLCFP, eval_LCFP_add],
  ext x : 2,
  exact Completion.map_add
end

@[simp] lemma eval_CLCFP_sub [ϕ.suitable c₂ c₁] [ψ.suitable c₂ c₁] :
  (ϕ - ψ : universal_map m n).eval_CLCFP V r' c₁ c₂ =
  ϕ.eval_CLCFP V r' c₁ c₂ - ψ.eval_CLCFP V r' c₁ c₂ :=
begin
  simp only [eval_CLCFP, eval_LCFP_sub],
  ext x : 2,
  exact Completion.map_sub
end

open category_theory.limits

lemma eval_CLCFP_comp (g : universal_map m n) (f : universal_map l m)
  [hg : g.suitable c₂ c₁] [hf : f.suitable c₃ c₂] :
  @eval_CLCFP V r' c₁ c₃ _ _ (comp g f) (suitable.comp c₂) =
    g.eval_CLCFP V r' c₁ c₂ ≫ f.eval_CLCFP V r' c₂ c₃ :=
by simp only [eval_CLCFP, ← whisker_right_comp, eval_LCFP_comp V r' c₁ c₂ c₃]

lemma res_comp_eval_CLCFP
  [fact (c₂ ≤ c₁)] [ϕ.suitable c₄ c₂] [ϕ.suitable c₃ c₁] [fact (c₄ ≤ c₃)] :
  res V r' c₁ c₂ n ≫ ϕ.eval_CLCFP V r' c₂ c₄ =
    ϕ.eval_CLCFP V r' c₁ c₃ ≫ res V r' c₃ c₄ m :=
by { dsimp only [CLC, res], simp only [eval_CLCFP, ← whisker_right_comp, ← whisker_right_twice],
     congr' 1, apply res_comp_eval_LCFP }

lemma Tinv_comp_eval_CLCFP [fact (0 < r')] [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [ϕ.suitable c₃ c₁] [ϕ.suitable c₄ c₂] :
  Tinv V r' c₁ c₂ n ≫ ϕ.eval_CLCFP V r' c₂ c₄ =
    ϕ.eval_CLCFP V r' c₁ c₃ ≫ Tinv V r' c₃ c₄ m :=
by simp only [eval_CLCFP, Tinv_def, ← whisker_right_comp]; congr' 1; apply Tinv_comp_eval_LCFP

lemma T_inv_comp_eval_CLCFP [normed_with_aut r V] [fact (0 < r)] [ϕ.suitable c₂ c₁] :
  T_inv r V r' c₁ n ≫ ϕ.eval_CLCFP V r' c₁ c₂ =
    ϕ.eval_CLCFP V r' c₁ c₂ ≫ T_inv r V r' c₂ m :=
by simp only [eval_CLCFP, T_inv_def, ← whisker_right_comp, T_inv_comp_eval_LCFP]

lemma eval_CLCFP_bound_by [normed_with_aut r V] [fact (0 < r)] [ϕ.suitable c₂ c₁]
  (N : ℕ) (h : ϕ.bound_by N) (M) :
  ((ϕ.eval_CLCFP V r' c₁ c₂).app M).bound_by N :=
Completion_map_bound_by _ _ $ eval_LCFP_bound_by _ _ _ _ _ _ _ h _

end universal_map

end breen_deligne
