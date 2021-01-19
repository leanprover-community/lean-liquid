import topology.subset_properties

variables {ι : Type*} (X : ι → Type*)
variables [fintype ι] [∀ i, topological_space (X i)] [∀ i, discrete_topology (X i)]

instance Pi.discrete_topology : discrete_topology (Π i, X i) :=
begin
  rw ← singletons_open_iff_discrete,
  intro x,
  rw show {x} = ⋂ i, {y : Π i, X i | y i = x i},
  { ext, simp only [function.funext_iff, set.mem_singleton_iff, set.mem_Inter, set.mem_set_of_eq] },
  apply is_open_Inter,
  intro i,
  exact (continuous_apply i).is_open_preimage _ (is_open_discrete {x i})
end
#lint- only unused_arguments
