import polyhedral_lattice.basic
import normed_group.pseudo_normed_group
import pseudo_normed_group.with_Tinv

noncomputable theory
open_locale nnreal

namespace polyhedral_lattice

open pseudo_normed_group

variables (Λ : Type*) (r' : ℝ≥0) (M : Type*)
variables [normed_group Λ] [polyhedral_lattice Λ]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]

instance : discrete_topology Λ :=
sorry

lemma filtration_finite (c : ℝ≥0) : (filtration Λ c).finite :=
sorry

instance filtration_fintype (c : ℝ≥0) : fintype (filtration Λ c) :=
(filtration_finite Λ c).fintype

instance : profinitely_filtered_pseudo_normed_group Λ :=
{ compact := λ c, by apply_instance, -- compact of finite
  continuous_add' := λ _ _, continuous_of_discrete_topology,
  continuous_neg' := λ _, continuous_of_discrete_topology,
  continuous_cast_le := λ _ _ _, continuous_of_discrete_topology,
  .. (show pseudo_normed_group Λ, by apply_instance) }

include r'

instance add_monoid_hom.profinitely_filtered_pseudo_normed_group :
  profinitely_filtered_pseudo_normed_group (Λ →+ M) :=
{ topology := λ c, sorry,
  t2 := sorry,
  td := sorry,
  compact := sorry,
  continuous_add' := sorry,
  continuous_neg' := sorry,
  continuous_cast_le := sorry,
  .. (show pseudo_normed_group (Λ →+ M), by apply_instance) }

def Tinv' : (Λ →+ M) →+ (Λ →+ M) :=
add_monoid_hom.comp_hom
  (@profinitely_filtered_pseudo_normed_group_with_Tinv.Tinv r' M _).to_add_monoid_hom

variables {Λ r' M}

lemma Tinv'_mem_filtration (c : ℝ≥0) (x : Λ →+ M) (hx : x ∈ filtration (Λ →+ M) c) :
  (Tinv' Λ r' M) x ∈ filtration (Λ →+ M) (r'⁻¹ * c) :=
sorry

variables (Λ r' M)

def Tinv : profinitely_filtered_pseudo_normed_group_hom (Λ →+ M) (Λ →+ M) :=
profinitely_filtered_pseudo_normed_group_hom.mk' (Tinv' Λ r' M)
begin
  refine ⟨r'⁻¹, λ c, ⟨Tinv'_mem_filtration c, _⟩⟩,
  sorry
end

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (Λ →+ M) :=
{ Tinv := sorry,
  Tinv_mem_filtration := sorry,
  .. (show profinitely_filtered_pseudo_normed_group (Λ →+ M), by apply_instance) }

end polyhedral_lattice
