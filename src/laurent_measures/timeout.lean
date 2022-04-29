import laurent_measures.ses

noncomputable theory


open laurent_measures pseudo_normed_group comphaus_filtered_pseudo_normed_group
open comphaus_filtered_pseudo_normed_group_hom
open_locale big_operators nnreal

namespace laurent_measures_ses

section theta

open theta real_measures

parameter (p : ℝ≥0)
local notation `r` := @r p
local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r

variable {S : Fintype}

local notation `ϖ` := Fintype.of (unit)

variable [fact (0 < p)]
variable [fact (p < 1)]

variable (S)

open theta metric real_measures

variable (c : ℝ≥0)

noncomputable! lemma test2 (ε η : ℝ) (y : closed_ball (0 : ℝ) (c ^ (p⁻¹ : ℝ)))
  (F : filtration (ℒ ϖ) c)
  (hF : |(((real_measures.homeo_filtration_ϖ_ball c) (θ_c p c (Fintype.of unit) F)) : ℝ) - y| < ε)
  (hη : η = ε - |(real_measures.homeo_filtration_ϖ_ball c (θ_c p c ϖ F)) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ))
  (answer : (U p c F (geom_B p c ((η / 2) ^ (p : ℝ)) h_pos) )  ⊆ ((real_measures.homeo_filtration_ϖ_ball c) ∘ θ_c p c (ϖ) ⁻¹' (ball y ε)))

   :
  (U p c F (geom_B p c ((η / 2) ^ (p : ℝ)) h_pos) )  ⊆ ((real_measures.homeo_filtration_ϖ_ball c) ∘ θ_c p c (ϖ) ⁻¹' (ball y ε))
  :=
begin
  intros G hG,
  let ξ_F : ℝ := ((real_measures.homeo_filtration_ϖ_ball c) (θ_c p c (Fintype.of unit) F)),
  let ξ_G : ℝ := ((real_measures.homeo_filtration_ϖ_ball c) (θ_c p c (Fintype.of unit) G)),
  simp only [set.mem_preimage, one_mul, eq_self_iff_true, eq_mpr_eq_cast, set_coe_cast,
  function.comp_app, mem_ball, subtype.dist_eq, real.dist_eq],
  have hp : 0 < (p : ℝ), { rw [← nnreal.coe_zero, nnreal.coe_lt_coe], from fact.out _ },
  have η_pos' : 0 < η := by {rw hη, from (sub_pos.mpr hF)},
  set η₀ : ℝ≥0 := ⟨η, le_of_lt η_pos'⟩ with hη₀,
  have h_η_η₀ := @coe_pow_half p _ _ η η_pos' η₀ hη₀,
  simp_rw [h_η_η₀] at hG,
  have speed_1 : |ξ_G - y | ≤ |ξ_G - ξ_F| + |ξ_F - y | := abs_sub_le ξ_G ξ_F y,
  have speed_2 : |ξ_G - ξ_F| + |ξ_F - y | < ε - | ξ_F - y | + | ξ_F - y | := by { apply add_lt_add_right,
                        rw [← real_measures.real_measures.dist_eq, ← real.rpow_lt_rpow_iff
                        (real.rpow_nonneg_of_nonneg (real_measures.real_measures.norm_nonneg _) _)
                        (sub_nonneg.mpr (le_of_lt hF)) hp, ← real.rpow_mul
                        (real_measures.real_measures.norm_nonneg _), inv_mul_cancel (ne_of_gt hp), real.rpow_one,
                        ← hη], exact dist_lt_of_mem_U p c (η₀ ^ (p : ℝ))
                        (real.rpow_pos_of_pos η_pos' _) F G hG},
  replace speed_2 : |ξ_G - ξ_F| + |ξ_F - y | < ε := by {rwa [sub_add_cancel ε (| ξ_F - y |)]
    at speed_2},
  exact lt_of_le_of_lt speed_1 speed_2,
  sorry
  end
#exit
