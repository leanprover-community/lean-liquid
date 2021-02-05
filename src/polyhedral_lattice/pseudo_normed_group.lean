import polyhedral_lattice.basic
import normed_group.pseudo_normed_group
import pseudo_normed_group.system_of_complexes -- ← minimize

open_locale nnreal

namespace polyhedral_lattice

variables (Λ : Type*) (r' : ℝ≥0) (M : Type*)
variables [normed_group Λ] [polyhedral_lattice Λ]
variables [profinitely_filtered_pseudo_normed_group_with_Tinv r' M]

example : pseudo_normed_group Λ := by apply_instance

instance : profinitely_filtered_pseudo_normed_group Λ :=
sorry

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (Λ →+ M) :=
sorry

end polyhedral_lattice
