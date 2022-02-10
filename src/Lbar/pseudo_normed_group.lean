import pseudo_normed_group.with_Tinv
import Lbar.Lbar_le

/-!

# Lbar_r(S) is a profinitely filtered pseudo-normed group with T⁻¹

This file constructs this instance.

-/

universe u

noncomputable theory
open_locale big_operators nnreal

variables {r' : ℝ≥0} {S : Type u} [fact (0 < r')] [fintype S] {c c₁ c₂ c₃ : ℝ≥0}

namespace Lbar

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (Lbar r' S) :=
{ Tinv := comphaus_filtered_pseudo_normed_group_hom.mk' Lbar.Tinv
  begin
    refine ⟨r'⁻¹, λ c, ⟨_, _⟩⟩,
    { intros x hx, exact Lbar.Tinv_mem_filtration hx },
    { exact Lbar_le.continuous_Tinv _ _ _ _ }
  end,
  Tinv_mem_filtration := λ c x hx, Lbar.Tinv_mem_filtration hx,
  .. Lbar.profinitely_filtered_pseudo_normed_group }

@[simp] lemma Tinv_apply (F : Lbar r' S) :
  profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv F = F.Tinv := rfl

end Lbar

#lint-
