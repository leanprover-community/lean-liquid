import topology.subset_properties

variables {ι : Type*} (X : ι → Type*)
variables [fintype ι] [∀ i, topological_space (X i)] [∀ i, discrete_topology (X i)]

-- PR'd as https://github.com/leanprover-community/mathlib/pull/6088
/-- A finite product of discrete spaces is discrete. -/
instance Pi.discrete_topology : discrete_topology (Π i, X i) :=
singletons_open_iff_discrete.mp (λ x,
begin
  rw show {x} = ⋂ i, {y : Π i, X i | y i = x i},
  { ext, simp only [function.funext_iff, set.mem_singleton_iff, set.mem_Inter, set.mem_set_of_eq] },
  exact is_open_Inter (λ i, (continuous_apply i).is_open_preimage {x i} (is_open_discrete {x i}))
end)
#lint- only unused_arguments def_lemma doc_blame
