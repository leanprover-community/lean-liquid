import pseudo_normed_group.with_Tinv
import Mbar.Mbar_le
/-!

# Mbar_r(S) is a profinitely filtered pseudo-normed group with T⁻¹

This file constructs this instance.

-/
universe u

noncomputable theory
open_locale big_operators nnreal
open pseudo_normed_group
local attribute [instance] type_pow

variables {r' : ℝ≥0} {S : Type u} [fact (0 < r')] [fintype S] {c c₁ c₂ c₃ : ℝ≥0}

namespace Mbar

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (Mbar r' S) :=
{ Tinv := profinitely_filtered_pseudo_normed_group_hom.mk' Mbar.Tinv
  begin
    refine ⟨r'⁻¹, λ c, ⟨_, _⟩⟩,
    { intros x hx, exact Mbar.Tinv_mem_filtration hx },
    { exact Mbar_le.continuous_Tinv _ _ _ _ }
  end,
  Tinv_mem_filtration := λ c x hx, Mbar.Tinv_mem_filtration hx,
  .. Mbar.profinitely_filtered_pseudo_normed_group }

end Mbar
