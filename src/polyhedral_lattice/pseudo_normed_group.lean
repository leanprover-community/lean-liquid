import polyhedral_lattice.basic
import normed_group.pseudo_normed_group
import pseudo_normed_group.system_of_complexes -- ← minimize

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
  embedding_cast_le := sorry,
  .. (show pseudo_normed_group Λ, by apply_instance) }

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (Λ →+ M) :=
sorry

end polyhedral_lattice
