import pseudo_normed_group.LC
import locally_constant.Vhat

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

/-- The "functor" that sends `M` and `c` to `V-hat((filtration M c)^n)` -/
def CLCFP (V : NormedGroup) (r' : ℝ≥0) (M : Type*) (c : ℝ≥0) (n : ℕ)
  [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  NormedGroup :=
Completion.obj (LCFP V r' M c n)

namespace breen_deligne
namespace basic_universal_map

variables (M) {m n}

@[simps]
def eval_CLCFP [ϕ.suitable c₁ c₂] : CLCFP V r' M c₂ n ⟶ CLCFP V r' M c₁ m :=
Completion.map (ϕ.eval_LCFP V M c₁ c₂)

end basic_universal_map
end breen_deligne

open breen_deligne

namespace CLCFP

@[simps]
def map : CLCFP V r' M₂ c n ⟶ CLCFP V r' M₁ c n :=
Completion.map (LCFP.map V c n f)

variables (M)

@[simp] lemma map_id :
  map V c n (profinitely_filtered_pseudo_normed_group_with_Tinv_hom.id) = 𝟙 (CLCFP V r' M c n) :=
by { delta map, rw LCFP.map_id, apply category_theory.functor.map_id }

variables {M}

lemma map_comp : map V c n (g.comp f) = map V c n g ≫ map V c n f :=
by { delta map, rw LCFP.map_comp, apply category_theory.functor.map_comp }

lemma map_comp_eval_CLCFP [ϕ.suitable c₁ c₂] :
  map V c₂ n f ≫ ϕ.eval_CLCFP V M₁ c₁ c₂ = ϕ.eval_CLCFP V M₂ c₁ c₂ ≫ map V c₁ m f :=
begin
  delta map basic_universal_map.eval_CLCFP,
  simp only [← category_theory.functor.map_comp, ← op_comp, LCFP.map_comp_eval_LCFP],
end

@[simps]
def res [fact (c₁ ≤ c₂)] : CLCFP V r' M c₂ n ⟶ CLCFP V r' M c₁ n :=
Completion.map (LCFP.res V c₁ c₂ n)

@[simp] lemma res_refl : @res V r' M _ c c n _ = 𝟙 _ :=
by { delta res, rw LCFP.res_refl, apply category_theory.functor.map_id }

lemma map_comp_res [fact (c₁ ≤ c₂)] :
  map V c₂ n f ≫ res V c₁ c₂ n = res V c₁ c₂ n ≫ map V c₁ n f :=
by { delta map res, simp only [← category_theory.functor.map_comp, ← op_comp, LCFP.map_comp_res] }

include r'

lemma res_comp_eval_CLCFP
  [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
  res V c₃ c₄ n ≫ ϕ.eval_CLCFP V M c₁ c₃ = ϕ.eval_CLCFP V M c₂ c₄ ≫ res V c₁ c₂ m :=
begin
  delta res basic_universal_map.eval_CLCFP,
  simp only [← category_theory.functor.map_comp, ← op_comp,
    LCFP.res_comp_eval_LCFP V c₁ c₂ c₃ c₄]
end

omit r'

section Tinv
open profinitely_filtered_pseudo_normed_group_with_Tinv
variables [fact (0 < r')]

@[simps]
def Tinv : CLCFP V r' M c n ⟶ CLCFP V r' M (r' * c) n :=
Completion.map (LCFP.Tinv V c n)

lemma map_comp_Tinv :
  map V c n f ≫ Tinv V c n = Tinv V c n ≫ map V (r' * c) n f :=
by { delta Tinv map, simp only [← category_theory.functor.map_comp, ← op_comp, LCFP.map_comp_Tinv] }

lemma res_comp_Tinv [fact (c₁ ≤ c₂)] :
  res V c₁ c₂ n ≫ (@Tinv V r' M _ c₁ n _) = Tinv V c₂ n ≫ res V (r' * c₁) (r' * c₂) n :=
by { delta Tinv res, simp only [← category_theory.functor.map_comp, ← op_comp, LCFP.res_comp_Tinv] }

lemma Tinv_comp_eval_CLCFP [ϕ.suitable c₁ c₂] :
  Tinv V c₂ n ≫ ϕ.eval_CLCFP V M (r' * c₁) (r' * c₂) = ϕ.eval_CLCFP V M c₁ c₂ ≫ Tinv V c₁ m :=
begin
  delta Tinv basic_universal_map.eval_CLCFP,
  simp only [← category_theory.functor.map_comp, ← op_comp, LCFP.Tinv_comp_eval_LCFP V c₁ c₂],
end

end Tinv

end CLCFP
