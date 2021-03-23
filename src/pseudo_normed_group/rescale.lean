import pseudo_normed_group.with_Tinv
import polyhedral_lattice.rescale -- for the definition of `rescale`, maybe move that?

noncomputable theory

open_locale nnreal

namespace rescale

open pseudo_normed_group

variables (r r' : ℝ≥0) (M : Type*)

section pseudo_normed_group

variables [pseudo_normed_group M]

instance : pseudo_normed_group (rescale r M) :=
{ filtration := λ c, show set M, from filtration M (c * r⁻¹),
  filtration_mono := λ c₁ c₂ h, filtration_mono (mul_le_mul' h le_rfl),
  zero_mem_filtration := λ c, @zero_mem_filtration M _ _,
  neg_mem_filtration := λ c, @neg_mem_filtration M _ _,
  add_mem_filtration := λ c₁ c₂, by { simp only [add_mul], apply add_mem_filtration } }

lemma mem_filtration (x : rescale r M) (c : ℝ≥0) :
  x ∈ filtration (rescale r M) c ↔ (of.symm x) ∈ filtration M (c * r⁻¹) :=
iff.rfl

end pseudo_normed_group

section profinitely_filtered_pseudo_normed_group

open profinitely_filtered_pseudo_normed_group

variables [profinitely_filtered_pseudo_normed_group M]

instance : profinitely_filtered_pseudo_normed_group (rescale r M) :=
{ topology := by { delta rescale, apply_instance },
  t2 := by { delta rescale, apply_instance },
  td := by { delta rescale, apply_instance },
  compact := by { delta rescale, apply_instance },
  continuous_add' :=
  begin
    intros c₁ c₂,
    haveI : fact ((c₁ + c₂) * r⁻¹ ≤ c₁ * r⁻¹ + c₂ * r⁻¹) := le_of_eq (add_mul _ _ _),
    rw (embedding_cast_le ((c₁ + c₂) * r⁻¹) (c₁ * r⁻¹ + c₂ * r⁻¹)).continuous_iff,
    exact (continuous_add' (c₁ * r⁻¹) (c₂ * r⁻¹))
  end,
  continuous_neg' := λ c, continuous_neg' _,
  continuous_cast_le := λ c₁ c₂ h, by exactI continuous_cast_le _ _,
  .. rescale.pseudo_normed_group _ _ }

end profinitely_filtered_pseudo_normed_group

section profinitely_filtered_pseudo_normed_group_with_Tinv

open profinitely_filtered_pseudo_normed_group_with_Tinv
open profinitely_filtered_pseudo_normed_group

variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]

include r'

@[simps]
def Tinv' : rescale r M →+ rescale r M :=
{ to_fun := λ x, of $ Tinv $ of.symm x,
  map_zero' := by { delta rescale, exact Tinv.map_zero },
  map_add' := by { delta rescale, exact Tinv.map_add } }

lemma Tinv'_mem_filtration (c : ℝ≥0) (x : rescale r M) (hx : x ∈ filtration (rescale r M) c) :
  (Tinv' r r' M) x ∈ filtration (rescale r M) (r'⁻¹ * c) :=
by simpa only [mem_filtration, Tinv'_apply, equiv.symm_apply_apply, mul_assoc]
  using Tinv_mem_filtration _ _ hx

@[simps]
def Tinv : profinitely_filtered_pseudo_normed_group_hom (rescale r M) (rescale r M) :=
profinitely_filtered_pseudo_normed_group_hom.mk' (Tinv' r r' M)
begin
  refine ⟨r'⁻¹, λ c, ⟨Tinv'_mem_filtration r r' M c, _⟩⟩,
  haveI : fact (r'⁻¹ * (c * r⁻¹) ≤ r'⁻¹ * c * r⁻¹) := ge_of_eq (mul_assoc _ _ _),
  have := @Tinv₀_continuous r' M _ (c * r⁻¹),
  rw (embedding_cast_le (r'⁻¹ * (c * r⁻¹)) (r'⁻¹ * c * r⁻¹)).continuous_iff at this,
  exact this
end

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (rescale r M) :=
{ Tinv := rescale.Tinv r r' M,
  Tinv_mem_filtration := Tinv'_mem_filtration r r' M,
  .. rescale.profinitely_filtered_pseudo_normed_group r M }

end profinitely_filtered_pseudo_normed_group_with_Tinv

end rescale
