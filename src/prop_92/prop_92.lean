import pseudo_normed_group.CLC
import prop_92.concrete

noncomputable theory

open_locale nnreal

namespace CLCFP

variables (r r' : ℝ≥0) (V : SemiNormedGroup) [normed_with_aut r V] (c c₁ c₂ : ℝ≥0) (n : ℕ)
variables [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)]
variables (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ)

include r

def T_inv_sub_Tinv :=
CLCFP.res V r' c₁ c₂ n ≫ CLCFP.T_inv r V r' c₂ n - CLCFP.Tinv V r' c₁ c₂ n

lemma norm_T_inv_sub_Tinv_le : ∥(T_inv_sub_Tinv r r' V c₁ c₂ n).app M∥ ≤ (1 + r⁻¹) :=
begin
  rw [T_inv_sub_Tinv, sub_eq_neg_add],
  refine le_trans (norm_add_le _ _) (add_le_add _ _),
  { rw [category_theory.nat_trans.app_neg, norm_neg],
    refine le_trans (normed_group_hom.norm_completion _).le _,
    exact normed_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.1
      (SemiNormedGroup.LocallyConstant_obj_map_norm_noninc _ _ _ _) },
  { refine normed_group_hom.norm_comp_le_of_le' 1 r⁻¹ r⁻¹ (mul_one _).symm _ _,
    { exact CLC.norm_T_inv_le r V _ },
    { exact normed_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.1
      (res_norm_noninc V r' c₁ c₂ n M) } },
end

variables {V c n M}

open profinitely_filtered_pseudo_normed_group profinitely_filtered_pseudo_normed_group_with_Tinv
  comphaus_filtered_pseudo_normed_group
open locally_constant category_theory

/-- 9.2 of Analytic.pdf -/
lemma T_inv_sub_Tinv_exists_preimage [hr1 : fact (r < 1)]
  (f : (CLCFP V r' (r' * c) n).obj M) (ε : ℝ≥0) (hε : 0 < ε) :
  ∃ g : (CLCFP V r' c n).obj M, (T_inv_sub_Tinv r r' V c (r' * c) n).app M g = f ∧
    (∥g∥ ≤ (r / (1 - r) + ε) * ∥f∥) :=
begin
  obtain ⟨g, hg1, hg2⟩ := @concrete_92 _ _ _ _ _ _ _ _
    ((FiltrationPow.cast_le _ _ _ _).app _) (embedding_cast_le _ _)
    ((FiltrationPow.Tinv r' (r' * c) c _).app _) r V _ (Tinv₀_continuous _ _) hr1 _ f ε hε,
  refine ⟨g, _, hg2⟩,
  rw ← hg1, clear hg1,
  dsimp only [T_inv_sub_Tinv, CLC, T_inv, CLC.T_inv, Tinv, CLCFP.res,
    whisker_left_app, nat_trans.app_sub, nat_trans.comp_app, whisker_right_app,
    normed_group_hom.sub_apply, whisker_right_app, functor.comp_map],
  rw [← SemiNormedGroup.Completion.map_comp,
      ← normed_group_hom.sub_apply, ← functor.map_sub],
  refl
end

variables (V c n M)

lemma T_inv_sub_Tinv_surjective [fact (r < 1)] :
  function.surjective ((T_inv_sub_Tinv r r' V c (r' * c) n).app M) :=
begin
  intros f,
  obtain ⟨g, hg, -⟩ := T_inv_sub_Tinv_exists_preimage r r' f 1 zero_lt_one,
  exact ⟨g, hg⟩
end

end CLCFP
