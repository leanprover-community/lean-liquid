import pseudo_normed_group.LC
import locally_constant.Vhat

open_locale classical nnreal
noncomputable theory
local attribute [instance] type_pow

open NormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group

universe variable u
variables (r : ℝ≥0) (V : NormedGroup)
variables (r' : ℝ≥0) {M M₁ M₂ M₃ : Type u}
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₁]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₂]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₃]
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)
variables (f : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂)
variables (g : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₂ M₃)

/-- The "functor" that sends `M` and `c` to `V-hat((filtration M c)^n)` -/
def CLCFP (V : NormedGroup) (r' : ℝ≥0) (M : Type*) (c : ℝ≥0) (n : ℕ)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  NormedGroup :=
Completion.obj (LCFP V r' M c n)

namespace CLCFP

@[simps]
def map : CLCFP V r' M₂ c n ⟶ CLCFP V r' M₁ c n :=
Completion.map (LCFP.map V r' c n f)

variables (M)

@[simp] lemma map_id :
  map V r' c n (profinitely_filtered_pseudo_normed_group_with_Tinv_hom.id) =
    𝟙 (CLCFP V r' M c n) :=
by { delta map, rw LCFP.map_id, apply category_theory.functor.map_id }

variables {M}

lemma map_comp : map V r' c n (g.comp f) = map V r' c n g ≫ map V r' c n f :=
by { delta map, rw LCFP.map_comp, apply category_theory.functor.map_comp }

lemma map_norm_noninc : (map V r' c n f).norm_noninc :=
Completion_map_norm_noninc _ $ LCFP.map_norm_noninc _ _ _ _ _

@[simps]
def res [fact (c₁ ≤ c₂)] : CLCFP V r' M c₂ n ⟶ CLCFP V r' M c₁ n :=
Completion.map (LCFP.res V r' c₁ c₂ n)

@[simp] lemma res_refl : @res V r' M _ c c n _ = 𝟙 _ :=
by { delta res, rw LCFP.res_refl, apply category_theory.functor.map_id }

lemma res_comp_res [fact (c₁ ≤ c₂)] [fact (c₂ ≤ c₃)] [fact (c₁ ≤ c₃)] :
  res V r' c₂ c₃ n ≫ res V r' c₁ c₂ n = @res V r' M _ c₁ c₃ n _ :=
by simp only [res, ← category_theory.functor.map_comp, ← op_comp, LCFP.res_comp_res]

lemma res_norm_noninc [fact (c₁ ≤ c₂)] : (@res V r' M _ c₁ c₂ n _).norm_noninc :=
Completion_map_norm_noninc _ $ LCFP.res_norm_noninc _ _ _ _ _

lemma map_comp_res [fact (c₁ ≤ c₂)] :
  map V r' c₂ n f ≫ res V r' c₁ c₂ n = res V r' c₁ c₂ n ≫ map V r' c₁ n f :=
by simp only [map, res, ← category_theory.functor.map_comp, ← op_comp, LCFP.map_comp_res]

section Tinv
open profinitely_filtered_pseudo_normed_group_with_Tinv
variables [fact (0 < r')]

@[simps]
def Tinv : CLCFP V r' M c n ⟶ CLCFP V r' M (r' * c) n :=
Completion.map (LCFP.Tinv V r' c n)

lemma map_comp_Tinv :
  map V r' c n f ≫ Tinv V r' c n = Tinv V r' c n ≫ map V r' (r' * c) n f :=
by simp only [Tinv, map, ← category_theory.functor.map_comp, ← op_comp, LCFP.map_comp_Tinv]

lemma res_comp_Tinv [fact (c₁ ≤ c₂)] :
  res V r' c₁ c₂ n ≫ (@Tinv V r' M _ c₁ n _) = Tinv V r' c₂ n ≫ res V r' (r' * c₁) (r' * c₂) n :=
by simp only [Tinv, res, ← category_theory.functor.map_comp, ← op_comp, LCFP.res_comp_Tinv]

end Tinv

section T_inv

variables [normed_with_aut r V] [fact (0 < r)]

@[simps]
def T_inv : CLCFP V r' M c n ⟶ CLCFP V r' M c n :=
Completion.map (LCFP.T_inv r V r' c n)

lemma map_comp_T_inv :
  map V r' c n f ≫ T_inv r V r' c n = T_inv r V r' c n ≫ map V r' c n f :=
by simp only [T_inv, map, ← category_theory.functor.map_comp, ← op_comp, LCFP.map_comp_T_inv]

lemma res_comp_T_inv [fact (c₁ ≤ c₂)] :
  res V r' c₁ c₂ n ≫ (@T_inv r V r' M _ c₁ n _ _) =
    T_inv r V r' c₂ n ≫ res V r' c₁ c₂ n :=
by simp only [T_inv, res, ← category_theory.functor.map_comp, ← op_comp, LCFP.res_comp_T_inv]

end T_inv

end CLCFP

namespace breen_deligne

open CLCFP
variables (M) {l m n}

namespace basic_universal_map

variables (ϕ : basic_universal_map m n)

@[simps]
def eval_CLCFP : CLCFP V r' M c₂ n ⟶ CLCFP V r' M c₁ m :=
Completion.map (ϕ.eval_LCFP V r' M c₁ c₂)

lemma map_comp_eval_CLCFP [ϕ.suitable c₁ c₂] :
  map V r' c₂ n f ≫ ϕ.eval_CLCFP V r' M₁ c₁ c₂ = ϕ.eval_CLCFP V r' M₂ c₁ c₂ ≫ map V r' c₁ m f :=
by simp only [map, eval_CLCFP, ← category_theory.functor.map_comp, ← op_comp, map_comp_eval_LCFP]

lemma res_comp_eval_CLCFP
  [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
  res V r' c₃ c₄ n ≫ ϕ.eval_CLCFP V r' M c₁ c₃ =
    ϕ.eval_CLCFP V r' M c₂ c₄ ≫ res V r' c₁ c₂ m :=
by simp only [res, eval_CLCFP, ← category_theory.functor.map_comp, ← op_comp,
  res_comp_eval_LCFP V r' _ c₁ c₂ c₃ c₄]

lemma Tinv_comp_eval_CLCFP [fact (0 < r')] [ϕ.suitable c₁ c₂] :
  Tinv V r' c₂ n ≫ ϕ.eval_CLCFP V r' M (r' * c₁) (r' * c₂) =
    ϕ.eval_CLCFP V r' M c₁ c₂ ≫ Tinv V r' c₁ m :=
by simp only [Tinv, eval_CLCFP, ← category_theory.functor.map_comp, ← op_comp,
  Tinv_comp_eval_LCFP V r' _ c₁ c₂]

lemma T_inv_comp_eval_CLCFP [normed_with_aut r V] [fact (0 < r)] [ϕ.suitable c₁ c₂] :
  T_inv r V r' c₂ n ≫ ϕ.eval_CLCFP V r' M c₁ c₂ =
    ϕ.eval_CLCFP V r' M c₁ c₂ ≫ T_inv r V r' c₁ m :=
by simp only [T_inv, eval_CLCFP, ← category_theory.functor.map_comp, ← op_comp,
  T_inv_comp_eval_LCFP r V r' c₁ c₂]

end basic_universal_map

namespace universal_map

variables (ϕ : universal_map m n)

def eval_CLCFP : CLCFP V r' M c₂ n ⟶ CLCFP V r' M c₁ m :=
Completion.map (ϕ.eval_LCFP V r' M c₁ c₂)

@[simp] lemma eval_CLCFP_zero :
  (0 : universal_map m n).eval_CLCFP V r' M c₁ c₂ = 0 :=
by simp only [eval_CLCFP, eval_LCFP_zero, NormedGroup.Completion.map_zero]

open category_theory.limits

lemma eval_CLCFP_comp (g : universal_map m n) (f : universal_map l m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  (comp g f).eval_CLCFP V r' M c₁ c₃ =
    g.eval_CLCFP V r' M c₂ c₃ ≫ f.eval_CLCFP V r' M c₁ c₂ :=
by simp only [eval_CLCFP, ← functor.map_comp, eval_LCFP_comp V r' M c₁ c₂ c₃]

lemma map_comp_eval_CLCFP [ϕ.suitable c₁ c₂] :
  map V r' c₂ n f ≫ ϕ.eval_CLCFP V r' M₁ c₁ c₂ =
    ϕ.eval_CLCFP V r' M₂ c₁ c₂ ≫ map V r' c₁ m f :=
by simp only [eval_CLCFP, map, ← functor.map_comp, map_comp_eval_LCFP V r' c₁ c₂]

lemma res_comp_eval_CLCFP
  [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
  res V r' c₃ c₄ n ≫ ϕ.eval_CLCFP V r' M c₁ c₃ =
    ϕ.eval_CLCFP V r' M c₂ c₄ ≫ res V r' c₁ c₂ m :=
by simp only [eval_CLCFP, res, ← functor.map_comp, res_comp_eval_LCFP V r' _ c₁ c₂]

lemma Tinv_comp_eval_CLCFP [fact (0 < r')] [ϕ.suitable c₁ c₂] :
  Tinv V r' c₂ n ≫ ϕ.eval_CLCFP V r' M (r' * c₁) (r' * c₂) =
    ϕ.eval_CLCFP V r' M c₁ c₂ ≫ Tinv V r' c₁ m :=
by simp only [eval_CLCFP, Tinv, ← functor.map_comp, Tinv_comp_eval_LCFP V r' _ c₁ c₂]

lemma T_inv_comp_eval_CLCFP [normed_with_aut r V] [fact (0 < r)] [ϕ.suitable c₁ c₂] :
  T_inv r V r' c₂ n ≫ ϕ.eval_CLCFP V r' M₁ c₁ c₂ =
    ϕ.eval_CLCFP V r' M₁ c₁ c₂ ≫ T_inv r V r' c₁ m :=
by simp only [eval_CLCFP, T_inv, ← functor.map_comp, T_inv_comp_eval_LCFP r V r' c₁ c₂]

end universal_map

end breen_deligne
