import pseudo_normed_group.FiltrationPow
import locally_constant.NormedGroup

open_locale classical nnreal
noncomputable theory
local attribute [instance] type_pow

open NormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group

universe variable u
variables (V : NormedGroup)
variables {r' : ℝ≥0} {M M₁ M₂ M₃ : Type u}
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₁]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₂]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M₃]
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (m n : ℕ) (ϕ : basic_universal_map m n)
variables (f : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₁ M₂)
variables (g : profinitely_filtered_pseudo_normed_group_with_Tinv_hom r' M₂ M₃)

/-- The "functor" that sends `M` and `c` to `V((filtration M c)^n)` -/
def LCFP (V : NormedGroup) (r' : ℝ≥0) (M : Type*) (c : ℝ≥0) (n : ℕ)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  NormedGroup :=
(LocallyConstant.obj V).obj (op $ FiltrationPow r' M c n)

namespace breen_deligne
namespace basic_universal_map

variables (M) {m n}

@[simps]
def eval_LCFP [ϕ.suitable c₁ c₂] : LCFP V r' M c₂ n ⟶ LCFP V r' M c₁ m :=
(LocallyConstant.obj V).map (ϕ.eval_FP M c₁ c₂).op

end basic_universal_map
end breen_deligne

open breen_deligne

namespace LCFP

@[simps]
def map : LCFP V r' M₂ c n ⟶ LCFP V r' M₁ c n :=
(LocallyConstant.obj V).map (FiltrationPow.map c n f).op

variables (M)

@[simp] lemma map_id :
  map V c n (profinitely_filtered_pseudo_normed_group_with_Tinv_hom.id) = 𝟙 (LCFP V r' M c n) :=
by { delta map, rw FiltrationPow.map_id, apply category_theory.functor.map_id, }

variables {M}

lemma map_comp : map V c n (g.comp f) = map V c n g ≫ map V c n f :=
by { delta map, rw [FiltrationPow.map_comp, op_comp], apply category_theory.functor.map_comp }

lemma map_comp_eval_LCFP [ϕ.suitable c₁ c₂] :
  map V c₂ n f ≫ ϕ.eval_LCFP V M₁ c₁ c₂ = ϕ.eval_LCFP V M₂ c₁ c₂ ≫ map V c₁ m f :=
begin
  delta map basic_universal_map.eval_LCFP,
  rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp,
    ← op_comp, ← op_comp, FiltrationPow.map_comp_eval_FP]
end

@[simps]
def res [fact (c₁ ≤ c₂)] : LCFP V r' M c₂ n ⟶ LCFP V r' M c₁ n :=
(LocallyConstant.obj V).map (FiltrationPow.cast_le c₁ c₂ n).op

@[simp] lemma res_refl : @res V r' M _ c c n _ = 𝟙 _ :=
by { delta res, rw FiltrationPow.cast_le_refl, apply category_theory.functor.map_id }

lemma map_comp_res [fact (c₁ ≤ c₂)] :
  map V c₂ n f ≫ res V c₁ c₂ n = res V c₁ c₂ n ≫ map V c₁ n f :=
begin
  delta map res,
  rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp,
    ← op_comp, ← op_comp, FiltrationPow.map_comp_cast_le]
end

include r'

lemma res_comp_eval_LCFP
  [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
  res V c₃ c₄ n ≫ ϕ.eval_LCFP V M c₁ c₃ = ϕ.eval_LCFP V M c₂ c₄ ≫ res V c₁ c₂ m :=
begin
  delta res basic_universal_map.eval_LCFP,
  rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp,
    ← op_comp, ← op_comp, FiltrationPow.cast_le_comp_eval_FP c₁ c₂ c₃ c₄]
end

omit r'

section Tinv
open profinitely_filtered_pseudo_normed_group_with_Tinv
variables [fact (0 < r')]

@[simps]
def Tinv : LCFP V r' M c n ⟶ LCFP V r' M (r' * c) n :=
res V _ _ n ≫ (LocallyConstant.obj V).map (FiltrationPow.Tinv (r' * c) n).op

lemma map_comp_Tinv :
  map V c n f ≫ Tinv V c n = Tinv V c n ≫ map V (r' * c) n f :=
begin
  delta Tinv,
  rw [← category.assoc, map_comp_res, category.assoc, category.assoc],
  delta map,
  rw [← category_theory.functor.map_comp, ← category_theory.functor.map_comp,
    ← op_comp, ← op_comp, FiltrationPow.map_comp_Tinv]
end

lemma res_comp_Tinv [fact (c₁ ≤ c₂)] :
  res V c₁ c₂ n ≫ (@Tinv V r' M _ c₁ n _) = Tinv V c₂ n ≫ res V (r' * c₁) (r' * c₂) n :=
begin
  delta Tinv res,
  simp only [← category_theory.functor.map_comp, ← op_comp],
  refl
end

lemma Tinv_comp_eval_LCFP [ϕ.suitable c₁ c₂] :
  Tinv V c₂ n ≫ ϕ.eval_LCFP V M (r' * c₁) (r' * c₂) = ϕ.eval_LCFP V M c₁ c₂ ≫ Tinv V c₁ m :=
begin
  delta Tinv,
  rw [← category.assoc, ← res_comp_eval_LCFP V (r'⁻¹ * (r' * c₁)) c₁ (r'⁻¹ * (r' * c₂)) c₂,
    category.assoc, category.assoc],
  delta basic_universal_map.eval_LCFP res,
  simp only [← category_theory.functor.map_comp, ← op_comp, ← category.assoc,
    FiltrationPow.Tinv_comp_eval_FP (r' * c₁) (r' * c₂)],
end

end Tinv

end LCFP
