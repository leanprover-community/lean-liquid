import category_theory.preadditive.functor_category

import pseudo_normed_group.FP
import locally_constant.SemiNormedGroup
import locally_constant.Vhat

import for_mathlib.normed_group_hom
/-!

# The category of locally constant maps

Various constructions of pseudo-normed groups of locally constant functions.

## Main definitions

- `LC V`: the functor sending a profinite set `S` to the locally constant
  functions from `S` to `V`
- `LCFP V r' c n`: the functor sending a profinitely filtered pseudo-normed
  group with T⁻¹ to V(M_c^n), the locally constant functions from M_c^n to V.

-/
namespace category_theory
namespace nat_trans

@[simp] lemma op_comp {C D} [category C] [category D]
  {F G H : C ⥤ D} {α : F ⟶ G} {β : G ⟶ H} :
  nat_trans.op (α ≫ β) = nat_trans.op β ≫ nat_trans.op α := rfl

end nat_trans
end category_theory

open_locale classical nnreal big_operators
noncomputable theory
local attribute [instance] type_pow

open SemiNormedGroup opposite Profinite pseudo_normed_group category_theory breen_deligne
open profinitely_filtered_pseudo_normed_group

universe variable u
variables (r : ℝ≥0) (V : SemiNormedGroup) (r' : ℝ≥0)
variables (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)

/-- `LC V n` is the functor that sends a profinite set `S` to `V(S)` -/
def LC (V : SemiNormedGroup) : Profiniteᵒᵖ ⥤ SemiNormedGroup :=
LocallyConstant.obj V

namespace LC

lemma map_norm_noninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((LC V).map f).norm_noninc :=
locally_constant.comap_hom_norm_noninc _ _

instance obj.normed_with_aut [normed_with_aut r V] [fact (0 < r)] (A : Profiniteᵒᵖ) :
  normed_with_aut r ((LC V).obj A) :=
SemiNormedGroup.normed_with_aut_LocallyConstant _ _ _

@[simps hom_app_apply inv_app_apply {fully_applied := ff}]
def T [normed_with_aut r V] : LC V ≅ LC V :=
LocallyConstant.map_iso normed_with_aut.T

lemma T_eq [normed_with_aut r V] [fact (0 < r)] (A) :
  (T r V).hom.app A = normed_with_aut.T.hom := rfl

lemma norm_T_le [normed_with_aut r V] [fact (0 < r)] (A) :
  ∥(LC.T r V).hom.app A∥ ≤ r :=
begin
  rw T_eq,
  refine normed_group_hom.op_norm_le_bound _ (nnreal.zero_le_coe) (λ v, _),
  exact le_of_eq (normed_with_aut.norm_T v)
end

@[simps {fully_applied := ff}]
def T_inv [normed_with_aut r V] : LC V ⟶ LC V :=
(LocallyConstant.map (normed_with_aut.T.inv : V ⟶ V) : _)

lemma T_inv_eq [normed_with_aut r V] : (T r V).inv = T_inv r V := rfl

lemma T_inv_eq' [normed_with_aut r V] [fact (0 < r)] (A) :
  (T_inv r V).app A = normed_with_aut.T.inv := rfl

lemma norm_T_inv_le [normed_with_aut r V] [fact (0 < r)] (A) :
  ∥(T_inv r V).app A∥ ≤ r⁻¹ :=
begin
  rw T_inv_eq',
  refine normed_group_hom.op_norm_le_bound _ (inv_nonneg.2 (nnreal.zero_le_coe)) (λ v, _),
  exact (normed_with_aut.norm_T_inv _ v).le
end

end LC

/-- The "functor" that sends `M` and `c` to `V((filtration M c)^n)` -/
def LCFP (V : SemiNormedGroup) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup :=
(FiltrationPow r' c n).op ⋙ LC V

theorem LCFP_def (V : SemiNormedGroup) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  LCFP V r' c n = (FiltrationPow r' c n).op ⋙ LocallyConstant.obj V := rfl

namespace LCFP

lemma map_norm_noninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((LCFP V r' c n).map f).norm_noninc :=
LC.map_norm_noninc _ _

@[simps {fully_applied := ff}]
def res (r' : ℝ≥0) (c₁ c₂ : ℝ≥0) [fact (c₂ ≤ c₁)] (n : ℕ) : LCFP V r' c₁ n ⟶ LCFP V r' c₂ n :=
(whisker_right (nat_trans.op (FiltrationPow.cast_le r' c₂ c₁ n)) (LocallyConstant.obj V) : _)

@[simp] lemma res_refl : res V r' c c n = 𝟙 _ :=
by { simp [res, FiltrationPow.cast_le_refl], refl }

lemma res_comp_res [h₁ : fact (c₃ ≤ c₂)] [h₂ : fact (c₂ ≤ c₁)] :
  res V r' c₁ c₂ n ≫ res V r' c₂ c₃ n = @res V r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ n :=
by simp only [res, ← whisker_right_comp, ← nat_trans.op_comp, FiltrationPow.cast_le_comp]

lemma res_norm_noninc [fact (c₂ ≤ c₁)] (M) : ((res V r' c₁ c₂ n).app M).norm_noninc :=
locally_constant.comap_hom_norm_noninc _ _

section Tinv
open profinitely_filtered_pseudo_normed_group_with_Tinv

@[simps {fully_applied := ff}]
def Tinv [fact (c₂ ≤ r' * c₁)] : LCFP V r' c₁ n ⟶ LCFP V r' c₂ n :=
(whisker_right (nat_trans.op $ FiltrationPow.Tinv r' c₂ c₁ n) (LocallyConstant.obj V) : _)

lemma Tinv_def [fact (c₂ ≤ r' * c₁)] : Tinv V r' c₁ c₂ n =
  whisker_right (nat_trans.op $ FiltrationPow.Tinv r' c₂ c₁ n) (LC V) := rfl

lemma res_comp_Tinv
  [fact (c₂ ≤ c₁)] [fact (c₃ ≤ c₂)] [fact (c₂ ≤ r' * c₁)] [fact (c₃ ≤ r' * c₂)] :
  res V r' c₁ c₂ n ≫ Tinv V r' c₂ c₃ n = Tinv V r' c₁ c₂ n ≫ res V r' c₂ c₃ n :=
begin
  simp only [Tinv, res, ← whisker_right_comp, ← nat_trans.op_comp],
  refl
end

lemma Tinv_norm_noninc [fact (c₂ ≤ r' * c₁)] (M) : ((Tinv V r' c₁ c₂ n).app M).norm_noninc :=
locally_constant.comap_hom_norm_noninc _ _

end Tinv

section normed_with_aut

variables [normed_with_aut r V]

instance [fact (0 < r)] (M) : normed_with_aut r ((LCFP V r' c n).obj M) :=
LC.obj.normed_with_aut _ _ _

@[simps {fully_applied := ff}]
def T : LCFP V r' c n ≅ LCFP V r' c n :=
((whiskering_left _ _ _).obj _).map_iso $ LC.T r _

@[simps app_apply {fully_applied := ff}]
def T_inv : LCFP V r' c n ⟶ LCFP V r' c n :=
(whisker_left _ (LC.T_inv r V) : _)

lemma T_inv_eq : (T r V r' c n).inv = T_inv r V r' c n := rfl

lemma T_inv_def :
  T_inv r V r' c n = (whisker_left  (FiltrationPow r' c n).op
      (LocallyConstant.map (normed_with_aut.T.inv : V ⟶ V)) : _) :=
rfl

end normed_with_aut

end LCFP

namespace breen_deligne

open LCFP

variables {l m n}

namespace basic_universal_map

variables (ϕ : basic_universal_map m n)

def eval_LCFP (c₁ c₂ : ℝ≥0) [ϕ.suitable c₂ c₁] : LCFP V r' c₁ n ⟶ LCFP V r' c₂ m :=
(whisker_right (nat_trans.op $ ϕ.eval_FP r' c₂ c₁) (LocallyConstant.obj V) : _)

def eval_LCFP' (c₁ c₂ : ℝ≥0) : LCFP V r' c₁ n ⟶ LCFP V r' c₂ m :=
if H : ϕ.suitable c₂ c₁
then by exactI (whisker_right (nat_trans.op $ ϕ.eval_FP r' c₂ c₁) (LocallyConstant.obj V) : _)
else 0

lemma eval_LCFP_eq_eval_LCFP' (h : ϕ.suitable c₂ c₁) :
  ϕ.eval_LCFP V r' c₁ c₂ = ϕ.eval_LCFP' V r' c₁ c₂ :=
by { delta eval_LCFP eval_LCFP', rw dif_pos h }

lemma eval_LCFP'_def [h : ϕ.suitable c₂ c₁] :
  ϕ.eval_LCFP' V r' c₁ c₂ =
    (whisker_right (nat_trans.op $ ϕ.eval_FP r' c₂ c₁) (LocallyConstant.obj V) : _) :=
dif_pos h

lemma eval_LCFP'_not_suitable (h : ¬ ϕ.suitable c₂ c₁) :
  ϕ.eval_LCFP' V r' c₁ c₂ = 0 :=
dif_neg h

lemma eval_LCFP'_comp (f : basic_universal_map m n) (g : basic_universal_map l m)
  [hf : f.suitable c₂ c₁] [hg : g.suitable c₃ c₂] :
  (basic_universal_map.comp f g).eval_LCFP' V r' c₁ c₃ = f.eval_LCFP' V r' c₁ c₂ ≫ g.eval_LCFP' V r' c₂ c₃ :=
begin
  haveI : (basic_universal_map.comp f g).suitable c₃ c₁ := suitable_comp c₂,
  simp only [eval_LCFP'_def, eval_FP_comp r' _ c₂, nat_trans.op_comp, whisker_right_comp]
end

lemma eval_LCFP_comp (f : basic_universal_map m n) (g : basic_universal_map l m)
  [hf : f.suitable c₂ c₁] [hg : g.suitable c₃ c₂] :
  @eval_LCFP V r' _ _ (basic_universal_map.comp f g) c₁ c₃ (suitable_comp c₂) =
    f.eval_LCFP V r' c₁ c₂ ≫ g.eval_LCFP V r' c₂ c₃ :=
by { simp only [eval_LCFP_eq_eval_LCFP'], apply eval_LCFP'_comp }

lemma res_comp_eval_LCFP
  [fact (c₂ ≤ c₁)] [fact (c₄ ≤ c₃)] [ϕ.suitable c₄ c₂] [ϕ.suitable c₃ c₁] :
  res V r' c₁ c₂ n ≫ ϕ.eval_LCFP V r' c₂ c₄ = ϕ.eval_LCFP V r' c₁ c₃ ≫ res V r' c₃ c₄ m :=
by simp only [res, eval_LCFP, ← whisker_right_comp, ← nat_trans.op_comp,
  cast_le_comp_eval_FP _ c₄ c₃ c₂ c₁]

lemma Tinv_comp_eval_LCFP [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [ϕ.suitable c₄ c₂] [ϕ.suitable c₃ c₁] :
  Tinv V r' c₁ c₂ n ≫ ϕ.eval_LCFP V r' c₂ c₄ = ϕ.eval_LCFP V r' c₁ c₃ ≫ Tinv V r' c₃ c₄ m :=
by simp only [Tinv, eval_LCFP, ← whisker_right_comp, ← nat_trans.op_comp,
  Tinv_comp_eval_FP _ _ c₄ c₃ c₂ c₁]

lemma T_inv_comp_eval_LCFP [normed_with_aut r V] [ϕ.suitable c₂ c₁] :
  T_inv r V r' c₁ n ≫ ϕ.eval_LCFP V r' c₁ c₂ = ϕ.eval_LCFP V r' c₁ c₂ ≫ T_inv r V r' c₂ m :=
begin
  ext M : 2,
  simp only [T_inv_def, eval_LCFP, nat_trans.comp_app,  whisker_right_app, whisker_left_app,
    nat_trans.naturality]
end

end basic_universal_map

namespace universal_map

open free_abelian_group

variables (ϕ : universal_map m n)

def eval_LCFP [ϕ.suitable c₂ c₁] : LCFP V r' c₁ n ⟶ LCFP V r' c₂ m :=
∑ g : {g : basic_universal_map m n // g ∈ ϕ.support},
  begin
    haveI := suitable_of_mem_support ϕ c₂ c₁ g g.2,
    exact coeff (g : basic_universal_map m n) ϕ • (basic_universal_map.eval_LCFP V r' g c₁ c₂)
  end

def eval_LCFP' : LCFP V r' c₁ n ⟶ LCFP V r' c₂ m :=
∑ g in ϕ.support, coeff g ϕ • (g.eval_LCFP' V r' c₁ c₂)

lemma eval_LCFP_eq_eval_LCFP' (h : ϕ.suitable c₂ c₁) :
  ϕ.eval_LCFP V r' c₁ c₂ = ϕ.eval_LCFP' V r' c₁ c₂ :=
begin
  simp only [eval_LCFP, eval_LCFP', basic_universal_map.eval_LCFP_eq_eval_LCFP',
    subtype.val_eq_coe],
  symmetry,
  apply finset.sum_subtype ϕ.support (λ _, iff.rfl),
end

@[simp] lemma eval_LCFP'_of (f : basic_universal_map m n) :
  eval_LCFP' V r' c₁ c₂ (of f) = f.eval_LCFP' V r' c₁ c₂ :=
by simp only [eval_LCFP', support_of, coeff_of_self, one_smul, finset.sum_singleton]

@[simp] lemma eval_LCFP_of (f : basic_universal_map m n) [f.suitable c₂ c₁] :
  eval_LCFP V r' c₁ c₂ (of f) = f.eval_LCFP V r' c₁ c₂ :=
by rw [eval_LCFP_eq_eval_LCFP', eval_LCFP'_of, basic_universal_map.eval_LCFP_eq_eval_LCFP']

@[simp] lemma eval_LCFP'_zero :
  (0 : universal_map m n).eval_LCFP' V r' c₁ c₂ = 0 :=
by rw [eval_LCFP', support_zero, finset.sum_empty]

@[simp] lemma eval_LCFP_zero :
  (0 : universal_map m n).eval_LCFP V r' c₁ c₂ = 0 :=
by rw [eval_LCFP_eq_eval_LCFP', eval_LCFP'_zero]

@[simp] lemma eval_LCFP'_neg (f : universal_map m n) :
  eval_LCFP' V r' c₁ c₂ (-f) = -f.eval_LCFP' V r' c₁ c₂ :=
by simp only [eval_LCFP', add_monoid_hom.map_neg, finset.sum_neg_distrib, neg_smul, support_neg]

@[simp] lemma eval_LCFP_neg (f : universal_map m n) [f.suitable c₂ c₁] :
  eval_LCFP V r' c₁ c₂ (-f) = -f.eval_LCFP V r' c₁ c₂ :=
by simp only [eval_LCFP_eq_eval_LCFP', eval_LCFP'_neg]

lemma eval_LCFP'_add (f g : universal_map m n) :
  eval_LCFP' V r' c₁ c₂ (f + g) = f.eval_LCFP' V r' c₁ c₂ + g.eval_LCFP' V r' c₁ c₂ :=
begin
  simp only [eval_LCFP'],
  rw finset.sum_subset (support_add f g), -- two goals
  simp only [add_monoid_hom.map_add _ f g, add_smul],
  convert finset.sum_add_distrib using 2, -- three goals
  apply finset.sum_subset (finset.subset_union_left _ _), swap,
  apply finset.sum_subset (finset.subset_union_right _ _),
  all_goals { rintros x - h, rw not_mem_support_iff at h, simp [h] },
end

lemma eval_LCFP_add (f g : universal_map m n) [f.suitable c₂ c₁] [g.suitable c₂ c₁] :
  eval_LCFP V r' c₁ c₂ (f + g) = f.eval_LCFP V r' c₁ c₂ + g.eval_LCFP V r' c₁ c₂ :=
by simp only [eval_LCFP_eq_eval_LCFP', eval_LCFP'_add]

lemma eval_LCFP_sub (f g : universal_map m n) [f.suitable c₂ c₁] [g.suitable c₂ c₁] :
  eval_LCFP V r' c₁ c₂ (f - g) = f.eval_LCFP V r' c₁ c₂ - g.eval_LCFP V r' c₁ c₂ :=
by simp only [sub_eq_add_neg, eval_LCFP_add, eval_LCFP_neg]

lemma eval_LCFP'_comp_of (g : basic_universal_map m n) (f : basic_universal_map l m)
  [hg : g.suitable c₂ c₁] [hf : f.suitable c₃ c₂] :
  eval_LCFP' V r' c₁ c₃ ((comp (of g)) (of f)) =
    eval_LCFP' V r' c₁ c₂ (of g) ≫ eval_LCFP' V r' c₂ c₃ (of f) :=
begin
  simp only [comp_of, eval_LCFP'_of],
  haveI hfg : (basic_universal_map.comp g f).suitable c₃ c₁ := basic_universal_map.suitable_comp c₂,
  rw ← basic_universal_map.eval_LCFP'_comp,
end

open category_theory category_theory.limits category_theory.preadditive

lemma eval_LCFP'_comp (g : universal_map m n) (f : universal_map l m)
  [hg : g.suitable c₂ c₁] [hf : f.suitable c₃ c₂] :
  (comp g f).eval_LCFP' V r' c₁ c₃ = g.eval_LCFP' V r' c₁ c₂ ≫ f.eval_LCFP' V r' c₂ c₃ :=
begin
  unfreezingI { revert hf },
  apply free_abelian_group.induction_on_free_predicate
    (suitable c₂ c₁) (suitable_free_predicate c₂ c₁) g hg; unfreezingI { clear_dependent g },
  { intros h₂,
    simp only [eval_LCFP'_zero, zero_comp, pi.zero_apply,
      add_monoid_hom.zero_apply, add_monoid_hom.map_zero] },
  { intros g hg hf,
    -- now do another nested induction on `f`
    apply free_abelian_group.induction_on_free_predicate
      (suitable c₃ c₂) (suitable_free_predicate c₃ c₂) f hf; unfreezingI { clear_dependent f },
    { simp only [eval_LCFP'_zero, comp_zero, add_monoid_hom.map_zero] },
    { intros f hf,
      rw suitable_of_iff at hf hg,
      resetI,
      apply eval_LCFP'_comp_of },
    { intros f hf IH,
      simp only [IH, eval_LCFP'_neg, add_monoid_hom.map_neg, comp_neg] },
    { rintros (f₁ : universal_map l m) (f₂ : universal_map l m) hf₁ hf₂ IH₁ IH₂, resetI,
      haveI Hg₁f : (comp (of g) f₁).suitable c₃ c₁ := suitable.comp c₂,
      haveI Hg₂f : (comp (of g) f₂).suitable c₃ c₁ := suitable.comp c₂,
      simp only [add_monoid_hom.map_add, eval_LCFP'_add, IH₁, IH₂, comp_add] } },
  { intros g hg IH hf, resetI, specialize IH,
    simp only [IH, add_monoid_hom.map_neg, eval_LCFP'_neg,
      add_monoid_hom.neg_apply, neg_inj, neg_comp] },
  { rintros (g₁ : universal_map m n) (g₂ : universal_map m n) hg₁ hg₂ IH₁ IH₂ hf, resetI,
    haveI Hg₁f : (comp g₁ f).suitable c₃ c₁ := suitable.comp c₂,
    haveI Hg₂f : (comp g₂ f).suitable c₃ c₁ := suitable.comp c₂,
    simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply, eval_LCFP'_add, IH₁, IH₂, add_comp] }
end

lemma eval_LCFP_comp (g : universal_map m n) (f : universal_map l m)
  [hg : g.suitable c₂ c₁] [hf : f.suitable c₃ c₂] :
  @eval_LCFP V r' c₁ c₃ _ _ (comp g f) (suitable.comp c₂) =
    g.eval_LCFP V r' c₁ c₂ ≫ f.eval_LCFP V r' c₂ c₃ :=
by { simp only [eval_LCFP_eq_eval_LCFP'], apply eval_LCFP'_comp }

lemma res_comp_eval_LCFP [fact (c₂ ≤ c₁)] [fact (c₄ ≤ c₃)] [ϕ.suitable c₃ c₁] [ϕ.suitable c₄ c₂] :
  res V r' c₁ c₂ n ≫ ϕ.eval_LCFP V r' c₂ c₄ = ϕ.eval_LCFP V r' c₁ c₃ ≫ res V r' c₃ c₄ m :=
begin
  simp only [eval_LCFP, comp_sum, sum_comp],
  apply finset.sum_congr rfl,
  rintros ⟨g, hg⟩ -,
  -- instead of this crazy `show`, we shoul prove `comp_gsmul` and `gsmul_comp`
  -- for preadditive categories
  show @comp_hom ((ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup) _ _ _ _ _ _ _ =
    @comp_hom ((ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup) _ _ _ _ _ _ _,
  simp only [add_monoid_hom.map_gsmul, add_monoid_hom.smul_apply],
  haveI : g.suitable c₃ c₁ := suitable_of_mem_support ϕ _ _ g hg,
  haveI : g.suitable c₄ c₂ := suitable_of_mem_support ϕ _ _ g hg,
  congr' 1,
  apply g.res_comp_eval_LCFP V r' c₁ c₂ c₃ c₄
end

lemma Tinv_comp_eval_LCFP [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [ϕ.suitable c₃ c₁] [ϕ.suitable c₄ c₂] :
  Tinv V r' c₁ c₂ n ≫ ϕ.eval_LCFP V r' c₂ c₄ = ϕ.eval_LCFP V r' c₁ c₃ ≫ Tinv V r' c₃ c₄ m :=
begin
  simp only [eval_LCFP, comp_sum, sum_comp],
  apply finset.sum_congr rfl,
  rintros ⟨g, hg⟩ -,
  show @comp_hom ((ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup) _ _ _ _ _ _ _ =
    @comp_hom ((ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup) _ _ _ _ _ _ _,
  simp only [add_monoid_hom.map_gsmul, add_monoid_hom.smul_apply],
  haveI : g.suitable c₃ c₁ := suitable_of_mem_support ϕ _ _ g hg,
  haveI : g.suitable c₄ c₂ := suitable_of_mem_support ϕ _ _ g hg,
  congr' 1,
  apply basic_universal_map.Tinv_comp_eval_LCFP V r'
end

lemma T_inv_comp_eval_LCFP [normed_with_aut r V] [ϕ.suitable c₂ c₁] :
  T_inv r V r' c₁ n ≫ ϕ.eval_LCFP V r' c₁ c₂ =
    ϕ.eval_LCFP V r' c₁ c₂ ≫ T_inv r V r' c₂ m :=
begin
  simp only [eval_LCFP, comp_sum, sum_comp],
  apply finset.sum_congr rfl,
  rintros ⟨g, hg⟩ -,
  show @comp_hom ((ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup) _ _ _ _ _ _ _ =
    @comp_hom ((ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroup) _ _ _ _ _ _ _,
  simp only [add_monoid_hom.map_gsmul, add_monoid_hom.smul_apply],
  haveI : g.suitable c₂ c₁ := suitable_of_mem_support ϕ _ _ g hg,
  congr' 1,
  apply basic_universal_map.T_inv_comp_eval_LCFP r V r'
end

lemma norm_eval_LCFP_le [ϕ.suitable c₂ c₁]
  (N : ℕ) (h : ϕ.bound_by N) (M) :
  ∥(ϕ.eval_LCFP V r' c₁ c₂).app M∥ ≤ N :=
begin
  rw [eval_LCFP_eq_eval_LCFP', eval_LCFP'],
  have : (∑ (g : basic_universal_map m n) in support ϕ, (coeff g ϕ).nat_abs : ℝ) ≤ N,
  { exact_mod_cast h },
  simp only [← nat_trans.app_hom_apply, add_monoid_hom.map_sum, add_monoid_hom.map_int_module_smul],
  refine le_trans (norm_sum_le_of_le ϕ.support _) this,
  intros g hg,
  have aux := ϕ.suitable_of_mem_support c₂ c₁ g hg,
  refine le_trans (norm_gsmul_le _ _) _,
  suffices : ∥(nat_trans.app_hom M) (basic_universal_map.eval_LCFP' V r' g c₁ c₂)∥ ≤ 1,
  { have aux₁ : ∥(coeff g) ϕ∥ = ↑(((coeff g) ϕ).nat_abs),
    { rw [@coe_coe ℕ ℤ ℝ _ _ _, ← int.abs_eq_nat_abs, int.cast_abs],
    refl },
    rw aux₁,
    exact mul_le_of_le_one_right ((coeff g) ϕ).nat_abs.cast_nonneg this },
  rw [← g.eval_LCFP_eq_eval_LCFP' V r' c₁ c₂, basic_universal_map.eval_LCFP],
  { apply normed_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.1,
    exact locally_constant.comap_hom_norm_noninc _ _, exact aux },
end

end universal_map

end breen_deligne
