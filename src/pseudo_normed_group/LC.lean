import pseudo_normed_group.FiltrationPow
import locally_constant.NormedGroup
import locally_constant.Vhat

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

/-- The functor that sends `A` to `V(A^n)` -/
def LCP (V : NormedGroup) (n : ℕ) : Profiniteᵒᵖ ⥤ NormedGroup :=
(Pow n).op ⋙ LocallyConstant.obj V

/-- The "functor" that sends `M` and `c` to `V((filtration M c)^n)` -/
def LCFP (V : NormedGroup) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ NormedGroup :=
(ProFiltPseuNormGrpWithTinv.level r' c).op ⋙ LCP V n

theorem LCFP_def (V : NormedGroup) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
  LCFP V r' c n = (FiltrationPow r' c n).op ⋙ LocallyConstant.obj V := rfl

namespace LCFP

lemma map_norm_noninc {M₁ M₂} (f : M₁ ⟶ M₂) :
  ((LCFP V r' c n).map f).norm_noninc :=
locally_constant.comap_hom_norm_noninc _ _

@[simps]
def res (r' : ℝ≥0) (c₁ c₂ : ℝ≥0) [fact (c₂ ≤ c₁)] (n : ℕ) : LCFP V r' c₁ n ⟶ LCFP V r' c₂ n :=
(whisker_right (nat_trans.op (FiltrationPow.cast_le r' c₂ c₁ n)) (LocallyConstant.obj V) : _)

@[simp] lemma res_refl : res V r' c c n = 𝟙 _ :=
by { simp [res, FiltrationPow.cast_le_refl], refl }

lemma res_comp_res [h₁ : fact (c₃ ≤ c₂)] [h₂ : fact (c₂ ≤ c₁)] :
  res V r' c₁ c₂ n ≫ res V r' c₂ c₃ n = @res V r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ n :=
by simp only [res, ← whisker_right_comp, ← nat_trans.op_comp, FiltrationPow.cast_le_comp]

lemma res_app [fact (c₂ ≤ c₁)] (M) :
  (res V r' c₁ c₂ n).app M =
    (LCP V n).map (Filtration.cast_le c₂ c₁ (unop M : ProFiltPseuNormGrpWithTinv r')).op :=
rfl

lemma res_norm_noninc [fact (c₂ ≤ c₁)] (M) : ((res V r' c₁ c₂ n).app M).norm_noninc :=
locally_constant.comap_hom_norm_noninc _ _

section Tinv
open profinitely_filtered_pseudo_normed_group_with_Tinv
variables [fact (0 < r')]

-- @[simps]
def Tinv (c c₂ : ℝ≥0) [fact (c₂ ≤ r' * c)] : LCFP V r' c n ⟶ LCFP V r' c₂ n :=
@whisker_right _ _ Profiniteᵒᵖ _ _ _ _ _
 (nat_trans.op $ FiltrationPow.Tinv r' c₂ c n) (LocallyConstant.obj V)

-- lemma map_comp_Tinv (c c₂ : ℝ≥0) [fact (c₂ ≤ r' * c)] {M₁ M₂} (f : M₁ ⟶ M₂) :
--   (LCFP V r' c n).map f ≫ Tinv V r' n c c₂ _ = Tinv V r' n c c₂ _ ≫ (LCFP V r' c₂ n).map f :=
-- begin
--   dsimp [Tinv, LCFP],
--   simp only [← (LCP V n).map_comp, ← op_comp],
--   congr' 2,
--   ext ⟨x, hx⟩,
--   exact f.unop.map_Tinv x
-- end

lemma res_comp_Tinv
  [fact (c₂ ≤ c₁)] [fact (c₃ ≤ c₂)] [fact (c₂ ≤ r' * c₁)] [fact (c₃ ≤ r' * c₂)] :
  res V r' c₁ c₂ n ≫ Tinv V r' n c₂ c₃ = Tinv V r' n c₁ c₂ ≫ res V r' c₂ c₃ n :=
begin
  simp only [Tinv, res, ← whisker_right_comp, ← nat_trans.op_comp],
  refl
end

lemma Tinv_norm_noninc [fact (c₂ ≤ r' * c₁)] (M) : ((Tinv V r' n c₁ c₂).app M).norm_noninc :=
locally_constant.comap_hom_norm_noninc _ _

end Tinv

section normed_with_aut

variables [normed_with_aut r V]

instance _root_.LCP.obj.normed_with_aut (A : Profiniteᵒᵖ) [fact (0 < r)] :
  normed_with_aut r ((LCP V n).obj A) :=
NormedGroup.normed_with_aut_LocallyConstant _ _ _

instance [fact (0 < r)] (M) : normed_with_aut r ((LCFP V r' c n).obj M) :=
LCP.obj.normed_with_aut _ _ _ _

def T_inv' [fact (0 < r)] : LCP V n ⟶ LCP V n :=
whisker_left _ (LocallyConstant.map (normed_with_aut.T.inv : V ⟶ V))

def T_inv [fact (0 < r)] : LCFP V r' c n ⟶ LCFP V r' c n :=
whisker_left _ (T_inv' r V n)

lemma T_inv_def [fact (0 < r)] :
  T_inv r V r' c n =
  @whisker_left _ _ Profiniteᵒᵖ _ _ _ (FiltrationPow r' c n).op
  _ _ (LocallyConstant.map (normed_with_aut.T.inv : V ⟶ V)) :=
rfl

lemma T_inv_app [fact (0 < r)] (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :
  (T_inv r V r' c n).app M =
    (T_inv' r V n).app ((ProFiltPseuNormGrpWithTinv.level r' c).op.obj M) :=
rfl

-- This does not apply to our situation
-- lemma T_inv_norm_noninc [fact (0 < r)] : (@T_inv r V r' M _ c n _ _).norm_noninc :=
-- begin
--   refine locally_constant.map_hom_norm_noninc _,
--   -- factor this out
--   intro v,
-- end

variables [fact (0 < r)]

lemma res_comp_T_inv [fact (c₂ ≤ c₁)] :
  res V r' c₁ c₂ n ≫ T_inv r V r' c₂ n = T_inv r V r' c₁ n ≫ res V r' c₁ c₂ n :=
begin
  ext M : 2,
  simp only [nat_trans.comp_app, res_app, T_inv_app],
  exact (T_inv' r V n).naturality _,
end

end normed_with_aut

end LCFP

namespace breen_deligne

open LCFP

variables (M) {l m n}

namespace basic_universal_map

variables (ϕ : basic_universal_map m n)

def eval_LCFP (c₁ c₂ : ℝ≥0) : LCFP V r' c₁ n ⟶ LCFP V r' c₂ m :=
if H : ϕ.suitable c₂ c₁
then by exactI whisker_right (nat_trans.op $ ϕ.eval_FP r' c₂ c₁) (LocallyConstant.obj V)
else 0

lemma eval_LCFP_def [h : ϕ.suitable c₂ c₁] :
  ϕ.eval_LCFP V r' c₁ c₂ =
    whisker_right (nat_trans.op $ ϕ.eval_FP r' c₂ c₁) (LocallyConstant.obj V) :=
dif_pos h

lemma eval_LCFP_comp (f : basic_universal_map m n) (g : basic_universal_map l m)
  [hf : f.suitable c₂ c₁] [hg : g.suitable c₃ c₂] :
  (f.comp g).eval_LCFP V r' c₁ c₃ =
  f.eval_LCFP V r' c₁ c₂ ≫ g.eval_LCFP V r' c₂ c₃ :=
begin
  haveI : (f.comp g).suitable c₃ c₁ := suitable_comp c₂,
  simp only [eval_LCFP_def, eval_FP_comp r' _ c₂, nat_trans.op_comp, whisker_right_comp]
end

lemma res_comp_eval_LCFP
  [fact (c₂ ≤ c₁)] [fact (c₄ ≤ c₃)] [ϕ.suitable c₄ c₂] [ϕ.suitable c₃ c₁] :
  res V r' c₁ c₂ n ≫ ϕ.eval_LCFP V r' c₂ c₄ = ϕ.eval_LCFP V r' c₁ c₃ ≫ res V r' c₃ c₄ m :=
by simp only [res, eval_LCFP_def, ← whisker_right_comp,
  ← nat_trans.op_comp, cast_le_comp_eval_FP _ c₄ c₃ c₂ c₁]

lemma Tinv_comp_eval_LCFP [fact (0 < r')] [fact (c₂ ≤ r' * c₁)] [fact (c₄ ≤ r' * c₃)]
  [ϕ.suitable c₄ c₂] [ϕ.suitable c₃ c₁] :
  Tinv V r' n c₁ c₂ ≫ ϕ.eval_LCFP V r' c₂ c₄ = ϕ.eval_LCFP V r' c₁ c₃ ≫ Tinv V r' m c₃ c₄ :=
by simp only [Tinv, eval_LCFP_def, ← whisker_right_comp,
    ← nat_trans.op_comp, Tinv_comp_eval_FP _ _ c₄ c₃ c₂ c₁]

lemma T_inv_comp_eval_LCFP [normed_with_aut r V] [fact (0 < r)] [ϕ.suitable c₂ c₁] :
  T_inv r V r' c₁ n ≫ ϕ.eval_LCFP V r' c₁ c₂ =
    ϕ.eval_LCFP V r' c₁ c₂ ≫ T_inv r V r' c₂ m :=
begin
  ext M : 2,
  simp only [T_inv_def, eval_LCFP_def, nat_trans.comp_app,
    whisker_right_app, whisker_left_app, nat_trans.naturality]
end

end basic_universal_map

namespace universal_map

open free_abelian_group

variables (ϕ : universal_map m n)

def eval_LCFP : LCFP V r' c₁ n ⟶ LCFP V r' c₂ m :=
∑ g in ϕ.support, coeff g ϕ • (g.eval_LCFP V r' c₁ c₂)

@[simp] lemma eval_LCFP_of (f : basic_universal_map m n) :
  eval_LCFP V r' c₁ c₂ (of f) = f.eval_LCFP V r' c₁ c₂ :=
by simp only [eval_LCFP, support_of, coeff_of_self, one_smul, finset.sum_singleton]

@[simp] lemma eval_LCFP_zero :
  (0 : universal_map m n).eval_LCFP V r' c₁ c₂ = 0 :=
by rw [eval_LCFP, support_zero, finset.sum_empty]

@[simp] lemma eval_LCFP_neg (f : universal_map m n) :
  eval_LCFP V r' c₁ c₂ (-f) = -f.eval_LCFP V r' c₁ c₂ :=
by simp only [eval_LCFP, add_monoid_hom.map_neg, finset.sum_neg_distrib, neg_smul, support_neg]

lemma eval_LCFP_add (f g : universal_map m n) :
  eval_LCFP V r' c₁ c₂ (f + g) =
    f.eval_LCFP V r' c₁ c₂ + g.eval_LCFP V r' c₁ c₂ :=
begin
  simp only [eval_LCFP],
  rw finset.sum_subset (support_add f g), -- two goals
  simp only [add_monoid_hom.map_add _ f g, add_smul],
  convert finset.sum_add_distrib using 2, -- three goals
  apply finset.sum_subset (finset.subset_union_left _ _), swap,
  apply finset.sum_subset (finset.subset_union_right _ _),
  all_goals { rintros x - h, rw not_mem_support_iff at h, simp [h] },
end

lemma eval_LCFP_comp_of (g : basic_universal_map m n) (f : basic_universal_map l m)
  [hg : g.suitable c₂ c₁] [hf : f.suitable c₃ c₂] :
  eval_LCFP V r' c₁ c₃ ((comp (of g)) (of f)) =
    eval_LCFP V r' c₁ c₂ (of g) ≫ eval_LCFP V r' c₂ c₃ (of f) :=
begin
  simp only [comp_of, eval_LCFP_of],
  haveI hfg : (g.comp f).suitable c₃ c₁ := basic_universal_map.suitable_comp c₂,
  rw ← basic_universal_map.eval_LCFP_comp,
end

open category_theory.limits

lemma eval_LCFP_comp (g : universal_map m n) (f : universal_map l m)
  [hg : g.suitable c₂ c₁] [hf : f.suitable c₃ c₂] :
  (comp g f).eval_LCFP V r' c₁ c₃ =
    g.eval_LCFP V r' c₁ c₂ ≫ f.eval_LCFP V r' c₂ c₃ :=
begin
  unfreezingI { revert hf },
  apply free_abelian_group.induction_on_free_predicate
    (suitable c₂ c₁) (suitable_free_predicate c₂ c₁) g hg; unfreezingI { clear_dependent g },
  { intros h₂,
    simp only [eval_LCFP_zero, zero_comp, pi.zero_apply,
      add_monoid_hom.coe_zero, add_monoid_hom.map_zero] },
  { intros g hg hf,
    -- now do another nested induction on `f`
    apply free_abelian_group.induction_on_free_predicate
      (suitable c₃ c₂) (suitable_free_predicate c₃ c₂) f hf; unfreezingI { clear_dependent f },
    { simp only [eval_LCFP_zero, comp_zero, add_monoid_hom.map_zero] },
    { intros f hf,
      rw suitable_of_iff at hf,
      resetI,
      apply eval_LCFP_comp_of },
    { intros f hf IH,
      simp only [IH, eval_LCFP_neg, add_monoid_hom.map_neg],
      refl },
    { rintros (f₁ : universal_map l m) (f₂ : universal_map l m) hf₁ hf₂ IH₁ IH₂, resetI,
      haveI Hg₁f : (comp (of g) f₁).suitable c₃ c₁ := suitable.comp c₂,
      haveI Hg₂f : (comp (of g) f₂).suitable c₃ c₁ := suitable.comp c₂,
      simp only [add_monoid_hom.map_add, eval_LCFP_add, IH₁, IH₂],
      refl } },
  { intros g hg IH hf, resetI, specialize IH,
    simp only [IH, add_monoid_hom.map_neg, eval_LCFP_neg,
      add_monoid_hom.neg_apply, neg_inj],
    refl },
  { rintros (g₁ : universal_map m n) (g₂ : universal_map m n) hg₁ hg₂ IH₁ IH₂ hf, resetI,
    haveI Hg₁f : (comp g₁ f).suitable c₁ c₃ := suitable.comp c₂,
    haveI Hg₂f : (comp g₂ f).suitable c₁ c₃ := suitable.comp c₂,
    simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply, eval_LCFP_add, IH₁, IH₂],
    show _ = normed_group_hom.comp_hom _ _,
    simpa [add_monoid_hom.map_add] }
end

lemma map_comp_eval_LCFP [ϕ.suitable c₁ c₂] :
  map V r' c₂ n f ≫ ϕ.eval_LCFP V r' M₁ c₁ c₂ = ϕ.eval_LCFP V r' M₂ c₁ c₂ ≫ map V r' c₁ m f :=
begin
  show normed_group_hom.comp_hom _ _ = normed_group_hom.comp_hom _ _,
  simp only [eval_LCFP_def, add_monoid_hom.map_sum, add_monoid_hom.sum_apply],
  apply finset.sum_congr rfl,
  intros g hg,
  haveI : g.suitable c₁ c₂ := suitable_of_mem_support ϕ c₁ c₂ g hg,
  simp only [← gsmul_eq_smul, add_monoid_hom.map_gsmul, add_monoid_hom.gsmul_apply],
  congr' 1,
  exact g.map_comp_eval_LCFP V r' _ _ _
end

lemma res_comp_eval_LCFP
  [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
  res V r' c₃ c₄ n ≫ ϕ.eval_LCFP V r' M c₁ c₃ = ϕ.eval_LCFP V r' M c₂ c₄ ≫ res V r' c₁ c₂ m :=
begin
  show normed_group_hom.comp_hom _ _ = normed_group_hom.comp_hom _ _,
  simp only [eval_LCFP_def, add_monoid_hom.map_sum, add_monoid_hom.sum_apply],
  apply finset.sum_congr rfl,
  intros g hg,
  simp only [← gsmul_eq_smul, add_monoid_hom.map_gsmul, add_monoid_hom.gsmul_apply],
  haveI : g.suitable c₂ c₄ := suitable_of_mem_support ϕ _ _ g hg,
  haveI : g.suitable c₁ c₃ := suitable_of_mem_support ϕ _ _ g hg,
  congr' 1,
  exact g.res_comp_eval_LCFP V r' M c₁ c₂ c₃ c₄
end

lemma Tinv_comp_eval_LCFP [fact (0 < r')] [ϕ.suitable c₁ c₂] :
  Tinv V r' c₂ n ≫ ϕ.eval_LCFP V r' M (r' * c₁) (r' * c₂) = ϕ.eval_LCFP V r' M c₁ c₂ ≫ Tinv V r' c₁ m :=
begin
  show normed_group_hom.comp_hom _ _ = normed_group_hom.comp_hom _ _,
  simp only [eval_LCFP_def, add_monoid_hom.map_sum, add_monoid_hom.sum_apply],
  apply finset.sum_congr rfl,
  intros g hg,
  haveI : g.suitable c₁ c₂ := suitable_of_mem_support ϕ c₁ c₂ g hg,
  simp only [← gsmul_eq_smul, add_monoid_hom.map_gsmul, add_monoid_hom.gsmul_apply],
  congr' 1,
  exact g.Tinv_comp_eval_LCFP V r' _ _ _
end

lemma T_inv_comp_eval_LCFP [normed_with_aut r V] [fact (0 < r)] [ϕ.suitable c₁ c₂] :
  T_inv r V r' c₂ n ≫ ϕ.eval_LCFP V r' M₁ c₁ c₂ =
    ϕ.eval_LCFP V r' M₁ c₁ c₂ ≫ T_inv r V r' c₁ m :=
begin
  show normed_group_hom.comp_hom _ _ = normed_group_hom.comp_hom _ _,
  simp only [eval_LCFP_def, add_monoid_hom.map_sum, add_monoid_hom.sum_apply],
  apply finset.sum_congr rfl,
  intros g hg,
  haveI : g.suitable c₁ c₂ := suitable_of_mem_support ϕ c₁ c₂ g hg,
  simp only [← gsmul_eq_smul, add_monoid_hom.map_gsmul, add_monoid_hom.gsmul_apply],
  congr' 1,
  exact g.T_inv_comp_eval_LCFP r V r' _ _
end

end universal_map

end breen_deligne
