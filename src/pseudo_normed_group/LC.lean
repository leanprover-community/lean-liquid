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
def res (r' : ℝ≥0) (c₁ c₂ : ℝ≥0) [fact (c₁ ≤ c₂)] (n : ℕ) : LCFP V r' c₂ n ⟶ LCFP V r' c₁ n :=
(whisker_right (nat_trans.op (FiltrationPow.cast_le r' c₁ c₂ n)) (LocallyConstant.obj V) : _)

@[simp] lemma res_refl : res V r' c c n = 𝟙 _ :=
by { simp [res, FiltrationPow.cast_le_refl], refl }

lemma res_comp_res [h₁ : fact (c₁ ≤ c₂)] [h₂ : fact (c₂ ≤ c₃)] :
  res V r' c₂ c₃ n ≫ res V r' c₁ c₂ n = @res V r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ n :=
by simp only [res, ← whisker_right_comp, ← nat_trans.op_comp, FiltrationPow.cast_le_comp]

lemma res_norm_noninc [fact (c₁ ≤ c₂)] (M) : ((@res V r' c₁ c₂ _ n).app M).norm_noninc :=
locally_constant.comap_hom_norm_noninc _ _

section Tinv
open profinitely_filtered_pseudo_normed_group_with_Tinv
variables [fact (0 < r')]

@[simps]
def Tinv : LCFP V r' M c n ⟶ LCFP V r' M (r' * c) n :=
(LCP V n).map (Tinv₀_hom _ _ c).op

lemma map_comp_Tinv :
  map V r' c n f ≫ Tinv V r' c n = Tinv V r' c n ≫ map V r' (r' * c) n f :=
begin
  delta Tinv,
  rw [← category.assoc, map_comp_res, category.assoc, category.assoc],
  delta map,
  simp only [← category_theory.functor.map_comp, ← op_comp, FiltrationPow.map_comp_Tinv]
end

lemma res_comp_Tinv [fact (c₁ ≤ c₂)] :
  res V r' c₁ c₂ n ≫ (@Tinv V r' M _ c₁ n _) =
    Tinv V r' c₂ n ≫ res V r' (r' * c₁) (r' * c₂) n :=
begin
  delta Tinv res,
  simp only [← category_theory.functor.map_comp, ← op_comp],
  refl
end

lemma Tinv_norm_noninc : (@Tinv V r' M _ c n _).norm_noninc :=
normed_group_hom.norm_noninc.comp
  (locally_constant.comap_hom_norm_noninc _ _)
  (res_norm_noninc V r' _ _ n)

end Tinv

section normed_with_aut

variables [normed_with_aut r V]

instance [fact (0 < r)] : normed_with_aut r (LCFP V r' M c n) :=
NormedGroup.normed_with_aut_LocallyConstant _ _ _

instance (A : Profiniteᵒᵖ) [fact (0 < r)] : normed_with_aut r ((LCP V n).obj A) :=
NormedGroup.normed_with_aut_LocallyConstant _ _ _

def T_inv' [fact (0 < r)] (A : Profiniteᵒᵖ) : (LCP V n).obj A ⟶ (LCP V n).obj A :=
normed_with_aut.T.inv

def T_inv [fact (0 < r)] : LCFP V r' M c n ⟶ LCFP V r' M c n :=
T_inv' r V n (op (of (filtration M c)))

lemma T_inv_eq [fact (0 < r)] :
  T_inv r V r' c n =
    (LocallyConstant.map (normed_with_aut.T.inv : V ⟶ V)).app (op $ FiltrationPow r' M c n) :=
rfl

-- This does not apply to our situation
-- lemma T_inv_norm_noninc [fact (0 < r)] : (@T_inv r V r' M _ c n _ _).norm_noninc :=
-- begin
--   refine locally_constant.map_hom_norm_noninc _,
--   -- factor this out
--   intro v,
-- end

variables [fact (0 < r)]

lemma map_comp_T_inv :
  map V r' c n f ≫ T_inv r V r' c n = T_inv r V r' c n ≫ map V r' c n f :=
(LocallyConstant.map (normed_with_aut.T.inv : V ⟶ V)).naturality _

lemma res_comp_T_inv [fact (c₁ ≤ c₂)] :
  res V r' c₁ c₂ n ≫ (@T_inv r V r' M _ c₁ n _ _) = T_inv r V r' c₂ n ≫ res V r' c₁ c₂ n :=
(LocallyConstant.map (normed_with_aut.T.inv : V ⟶ V)).naturality _

end normed_with_aut

end LCFP

namespace breen_deligne

open LCFP

variables (M) {l m n}

namespace basic_universal_map

variables (ϕ : basic_universal_map m n)

def eval_LCFP : LCFP V r' M c₂ n ⟶ LCFP V r' M c₁ m :=
if H : ϕ.suitable c₁ c₂
then by exactI (LocallyConstant.obj V).map (ϕ.eval_FP r' M c₁ c₂).op
else 0

lemma eval_LCFP_def [h : ϕ.suitable c₁ c₂] :
  ϕ.eval_LCFP V r' M c₁ c₂ = (LocallyConstant.obj V).map (ϕ.eval_FP r' M c₁ c₂).op :=
dif_pos h

lemma eval_LCFP_comp (g : basic_universal_map m n) (f : basic_universal_map l m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  (g.comp f).eval_LCFP V r' M c₁ c₃ =
  g.eval_LCFP V r' M c₂ c₃ ≫ f.eval_LCFP V r' M c₁ c₂ :=
begin
  haveI : (g.comp f).suitable c₁ c₃ := suitable_comp c₂,
  simp only [eval_LCFP_def],
  rw [← category_theory.functor.map_comp, ← op_comp],
  congr' 2,
  simp [eval_FP_comp r' M _ c₂],
end

lemma map_comp_eval_LCFP [ϕ.suitable c₁ c₂] :
  map V r' c₂ n f ≫ ϕ.eval_LCFP V r' M₁ c₁ c₂ = ϕ.eval_LCFP V r' M₂ c₁ c₂ ≫ map V r' c₁ m f :=
begin
  delta map,
  simp only [eval_LCFP_def, ← category_theory.functor.map_comp, ← op_comp, map_comp_eval_FP]
end

lemma res_comp_eval_LCFP
  [fact (c₁ ≤ c₂)] [ϕ.suitable c₂ c₄] [ϕ.suitable c₁ c₃] [fact (c₃ ≤ c₄)] :
  res V r' c₃ c₄ n ≫ ϕ.eval_LCFP V r' M c₁ c₃ = ϕ.eval_LCFP V r' M c₂ c₄ ≫ res V r' c₁ c₂ m :=
begin
  delta res,
  simp only [eval_LCFP_def, ← category_theory.functor.map_comp, ← op_comp,
    cast_le_comp_eval_FP _ _ c₁ c₂ c₃ c₄]
end

lemma Tinv_comp_eval_LCFP [fact (0 < r')] [ϕ.suitable c₁ c₂] :
  Tinv V r' c₂ n ≫ ϕ.eval_LCFP V r' M (r' * c₁) (r' * c₂) = ϕ.eval_LCFP V r' M c₁ c₂ ≫ Tinv V r' c₁ m :=
begin
  dsimp only [Tinv],
  rw [← category.assoc, ← res_comp_eval_LCFP V _ _ (r'⁻¹ * (r' * c₁)) c₁ (r'⁻¹ * (r' * c₂)) c₂,
    category.assoc, category.assoc],
  simp only [eval_LCFP_def, res, ← category_theory.functor.map_comp, ← op_comp,
    ← category.assoc, Tinv_comp_eval_FP _ _ (r' * c₁) (r' * c₂)],
end

lemma T_inv_comp_eval_LCFP [normed_with_aut r V] [fact (0 < r)] [ϕ.suitable c₁ c₂] :
  T_inv r V r' c₂ n ≫ ϕ.eval_LCFP V r' M₁ c₁ c₂ =
    ϕ.eval_LCFP V r' M₁ c₁ c₂ ≫ T_inv r V r' c₁ m :=
begin
  simp only [eval_LCFP_def],
  exact ((LocallyConstant.map (normed_with_aut.T.inv : V ⟶ V)).naturality _).symm
end

end basic_universal_map

namespace universal_map

open free_abelian_group

variables (ϕ : universal_map m n)

def eval_LCFP : LCFP V r' M c₂ n ⟶ LCFP V r' M c₁ m :=
if H : (ϕ.suitable c₁ c₂)
then by exactI
  ∑ g in ϕ.support, coeff g ϕ • (g.eval_LCFP V r' M c₁ c₂)
else 0

lemma eval_LCFP_def {m n : ℕ} (f : universal_map m n) [H : f.suitable c₁ c₂] :
  f.eval_LCFP V r' M c₁ c₂ = ∑ g in f.support, coeff g f • (g.eval_LCFP V r' M c₁ c₂) :=
dif_pos H

@[simp] lemma eval_LCFP_of (f : basic_universal_map m n) [f.suitable c₁ c₂] :
  eval_LCFP V r' M c₁ c₂ (of f) = f.eval_LCFP V r' M c₁ c₂ :=
by simp only [eval_LCFP_def, support_of, coeff_of_self, one_smul, finset.sum_singleton]

@[simp] lemma eval_LCFP_zero :
  (0 : universal_map m n).eval_LCFP V r' M c₁ c₂ = 0 :=
by rw [eval_LCFP_def, support_zero, finset.sum_empty]

@[simp] lemma eval_LCFP_neg (f : universal_map m n) :
  eval_LCFP V r' M c₁ c₂ (-f) = -f.eval_LCFP V r' M c₁ c₂ :=
begin
  rw eval_LCFP,
  split_ifs,
  { rw suitable_neg_iff at h,
    rw [eval_LCFP, dif_pos h],
    simp only [add_monoid_hom.map_neg, finset.sum_neg_distrib, neg_smul, support_neg] },
  { rw suitable_neg_iff at h,
    rw [eval_LCFP, dif_neg h, neg_zero] }
end

lemma eval_LCFP_add (f g : universal_map m n)
  [hf : f.suitable c₁ c₂] [hg : g.suitable c₁ c₂] :
  eval_LCFP V r' M c₁ c₂ (f + g) =
    f.eval_LCFP V r' M c₁ c₂ + g.eval_LCFP V r' M c₁ c₂ :=
begin
  simp only [eval_LCFP_def],
  rw finset.sum_subset (support_add f g), -- two goals
  simp only [add_monoid_hom.map_add _ f g, add_smul],
  convert finset.sum_add_distrib using 2, -- three goals
  apply finset.sum_subset (finset.subset_union_left _ _), swap,
  apply finset.sum_subset (finset.subset_union_right _ _),
  all_goals { rintros x - h, rw not_mem_support_iff at h, simp [h] },
end

lemma eval_LCFP_comp_of (g : basic_universal_map m n) (f : basic_universal_map l m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  eval_LCFP V r' M c₁ c₃ ((comp (of g)) (of f)) =
    eval_LCFP V r' M c₂ c₃ (of g) ≫ eval_LCFP V r' M c₁ c₂ (of f) :=
begin
  haveI hfg : (g.comp f).suitable c₁ c₃ := basic_universal_map.suitable_comp c₂,--hg.comp hf,
  simp only [comp_of, eval_LCFP_of],
  rw ← basic_universal_map.eval_LCFP_comp,
end

open category_theory.limits

lemma eval_LCFP_comp (g : universal_map m n) (f : universal_map l m)
  [hg : g.suitable c₂ c₃] [hf : f.suitable c₁ c₂] :
  (comp g f).eval_LCFP V r' M c₁ c₃ =
    g.eval_LCFP V r' M c₂ c₃ ≫ f.eval_LCFP V r' M c₁ c₂ :=
begin
  unfreezingI { revert hf },
  apply free_abelian_group.induction_on_free_predicate
    (suitable c₂ c₃) (suitable_free_predicate c₂ c₃) g hg; unfreezingI { clear_dependent g },
  { intros h₂,
    simp only [eval_LCFP_zero, zero_comp, pi.zero_apply,
      add_monoid_hom.coe_zero, add_monoid_hom.map_zero] },
  { intros g hg hf,
    -- now do another nested induction on `f`
    apply free_abelian_group.induction_on_free_predicate
      (suitable c₁ c₂) (suitable_free_predicate c₁ c₂) f hf; unfreezingI { clear_dependent f },
    { simp only [eval_LCFP_zero, comp_zero, add_monoid_hom.map_zero] },
    { intros f hf,
      rw suitable_of_iff at hf,
      resetI,
      apply eval_LCFP_comp_of },
    { intros f hf IH,
      show _ = normed_group_hom.comp_hom _ _,
      simp only [IH, pi.neg_apply, add_monoid_hom.map_neg, eval_LCFP_neg,
        add_monoid_hom.coe_neg, neg_inj],
      refl },
    { rintros (f₁ : universal_map l m) (f₂ : universal_map l m) hf₁ hf₂ IH₁ IH₂, resetI,
      haveI Hg₁f : (comp (of g) f₁).suitable c₁ c₃ := suitable.comp c₂,
      haveI Hg₂f : (comp (of g) f₂).suitable c₁ c₃ := suitable.comp c₂,
      simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply, eval_LCFP_add, IH₁, IH₂],
      show _ = normed_group_hom.comp_hom _ _,
      simpa [add_monoid_hom.map_add] } },
  { intros g hg IH hf, resetI, specialize IH,
    show _ = normed_group_hom.comp_hom _ _,
    simp only [IH, pi.neg_apply, add_monoid_hom.map_neg, eval_LCFP_neg,
      add_monoid_hom.coe_neg, neg_inj],
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
