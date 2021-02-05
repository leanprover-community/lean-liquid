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
{ to_add_comm_group := by apply_instance,
  filtration := pseudo_normed_group.filtration Λ,
  filtration_mono := pseudo_normed_group.filtration_mono,
  zero_mem_filtration := pseudo_normed_group.zero_mem_filtration,
  neg_mem_filtration := pseudo_normed_group.neg_mem_filtration,
  add_mem_filtration := pseudo_normed_group.add_mem_filtration,
  topology := λ _, uniform_space.to_topological_space,
  t2 := by apply_instance,
  td := _,
  compact := _,
  continuous_add' := _,
  continuous_neg' := _,
  embedding_cast_le := _,
}

instance : profinitely_filtered_pseudo_normed_group_with_Tinv r' (Λ →+ M) :=
sorry

end polyhedral_lattice
