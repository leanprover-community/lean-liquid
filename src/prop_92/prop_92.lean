import pseudo_normed_group.CLC
import prop_92.extension_profinite

noncomputable theory

open_locale nnreal

namespace CLCFP

variables {r r' : ℝ≥0} (V : SemiNormedGroup) [normed_with_aut r V] (c c₁ c₂ : ℝ≥0) (n : ℕ)
variables [fact (0 < r)] [fact (0 < r')] [fact (r' ≤ 1)] [fact (c₂ ≤ r' * c₁)] [fact (c₂ ≤ c₁)]
variables (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ)

include r

def Tinv_sub_T_inv :=
(CLCFP.Tinv V r' c₁ c₂ n).app M - (CLCFP.res V r' c₁ c₂ n ≫ CLCFP.T_inv r V r' c₂ n).app M

lemma Tinv_sub_T_inv_bound_by : (Tinv_sub_T_inv V c₁ c₂ n M).bound_by (r⁻¹ + 1) :=
begin
  rw [Tinv_sub_T_inv, sub_eq_neg_add],
  refine normed_group_hom.bound_by.add _ _,
  { refine (normed_group_hom.bound_by.comp' 1 r⁻¹ r⁻¹ (mul_one _).symm _ _).neg,
    { exact CLC.T_inv_bound_by r V _ },
    { exact (res_norm_noninc V r' c₁ c₂ n M).bound_by_one } },
  { refine SemiNormedGroup.Completion_map_bound_by _ _ _,
    exact (SemiNormedGroup.LocallyConstant_obj_map_norm_noninc _ _ _ _).bound_by_one },
end

variables {V c n M}

/-- 9.2 of Analytic.pdf -/
lemma Tinv_sub_T_inv_exists_preimage (f : (CLCFP V r' (r' * c) n).obj M) (ε : ℝ) (hε : 0 < ε) :
  ∃ g : (CLCFP V r' c n).obj M, Tinv_sub_T_inv V c (r' * c) n M g = f ∧
    (∥g∥ ≤ r / (1 - r) * (1 + ε) * ∥f∥) :=
begin
  sorry
end

variables (V c n M)

lemma Tinv_sub_T_inv_surjective : function.surjective (Tinv_sub_T_inv V c (r' * c) n M) :=
begin
  intros f,
  obtain ⟨g, hg, -⟩ := Tinv_sub_T_inv_exists_preimage f 1 zero_lt_one,
  exact ⟨g, hg⟩
end

end CLCFP
