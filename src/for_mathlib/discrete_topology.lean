import topology.subset_properties

variables {ι : Type*} (X : ι → Type*)
variables [fintype ι] [∀ i, topological_space (X i)] [∀ i, discrete_topology (X i)]

#lint- only unused_arguments def_lemma doc_blame
